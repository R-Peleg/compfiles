/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reuven Peleg (Problem statement)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Ring

import ProblemExtraction

problem_file {
  tags := [.NumberTheory]
}

/-!
# International Mathematical Olympiad 2025, Problem 3

Let N denote the set of positive integers.

A function f : N → N is said to be bonza if f(a) divides b ^ a − f(b) ^ f(a) for all positive integers a and b.

Determine the smallest real constant c such that f(n) ⩽ cn for all bonza functions f and all positive integers n.
-/
open Int

def Bonza (f : ℕ+ → ℕ+) : Prop :=
  ∀ a b : ℕ+,
    (f a : ℤ) ∣ (b ^ (a: ℕ) : ℤ) - (f b : ℤ) ^ ((f a): ℕ)

def is_valid_c (c : ℝ) : Prop :=
  ∀ (f : ℕ+ → ℕ+), Bonza f → ∀ n, (f n : ℝ) ≤ c * (n : ℝ)

determine answer : ℝ := 4

snip begin

def critical_bonza (n: ℕ+) : ℕ+ :=
  if (n: ℕ) % 2 = 1 then ⟨1, by decide⟩
  else if n = 4 then ⟨16, by decide⟩
  else ⟨2, by decide⟩


lemma odd_power_4_divisible_16(n : ℤ) (hn : Odd n) :
    (16 : ℤ) ∣ n^4 - 1 := by
  rw [show n^4 - 1 = (n ^ 2 + 1) * ((n + 1) * (n - 1)) by ring]

  have h1 : 2 ∣ n^2 + 1 := by
    exact hn.pow.add_one.two_dvd

  have h2 : (8: ℤ) ∣ (n + 1) * (n - 1) := by
    obtain ⟨k, rfl⟩ := hn
    rw [show (2 * k + 1 + 1) * (2 * k + 1 - 1) = 4 * (k * (k + 1)) by ring]
    obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
    rw [hm]
    rw [show 4 * (m + m) = (8: ℤ) * m by ring]
    use m

  conv =>
    lhs
    rw [show (16 : ℤ) = 2 * 8 by norm_num]
  exact Int.mul_dvd_mul h1 h2

lemma example_is_bonza: Bonza critical_bonza := by
  intro a b
  by_cases ha: (a: ℕ) % 2 = 1
  . -- a is odd
    simp [critical_bonza, ha]
  . -- a is even
    by_cases ha2 : a = 4
    · -- Subcase: a = 4
      have ha3 : ((4: ℕ+) : ℕ) % 2 = 0 := by decide
      simp [critical_bonza, ha2]
      -- prove divisibility by 16
      by_cases hb: (b: ℕ) % 2 = 1
      . -- Subsubcase: a = 4, b is odd
        simp [hb]
        have b_is_odd_z : Odd (b: ℤ) := by
          rw [Int.odd_coe_nat]
          exact Nat.odd_iff.mpr hb
        exact odd_power_4_divisible_16 (b: ℤ) b_is_odd_z
      .
        by_cases hb2: b = 4
        . -- Subsubsubcase: a = 4, b = 4
          simp [hb2]
        . -- Subsubsubcase: a = 4, b even, ≠ 4
          simp [hb, hb2]
          sorry
    · -- Subcase: f a = 2
      simp [critical_bonza, ha, ha2]
      have a_is_even_z : Even (a: ℤ) := by
        rw [Int.even_coe_nat]
        sorry
      by_cases hb: (b: ℕ) % 2 = 1
      . -- Subsubcase: f a = 2, b odd
        simp [hb]
        have b_is_odd_z : Odd (b: ℤ) := by
          rw [Int.odd_coe_nat]
          exact Nat.odd_iff.mpr hb
        apply Even.two_dvd
        have : Odd (-1) := by norm_num
        apply Odd.add_odd _ this
        exact b_is_odd_z.pow
      . -- Subsubcase: f a = 2, b even
        by_cases hb2: b = 4
        . -- Subsubsubcase: f a = 2, b = 4
          simp [hb2]
          apply Even.two_dvd
          have : Even (-256) := by decide
          apply Even.add _ this

          sorry
        . -- Subsubsubcase: f a = 2, b even, ≠ 4
          simp [hb, hb2]
          -- prove divisibility by 2 (cases on b)
          sorry


lemma c_at_least_4: Prop =
  ∀ c: ℝ, is_valid_c c → 4 ≤ c := by
  sorry

snip end

problem imo2025_p3 :
  IsLeast {c: ℝ | is_valid_c c} answer := by
  sorry
