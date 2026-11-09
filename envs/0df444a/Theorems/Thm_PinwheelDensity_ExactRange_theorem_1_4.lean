-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_theorem_1_4
-- name    : PinwheelDensity.ExactRange.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:39.979677+00:00
-- url     : https://prove2.me/theorems/5c27387f-f527-44b7-95fa-51b663846e58
-- title:
--   Theorem 1.4 — refutation for $a_1\ge 6$, all clauses and both families
-- statement:
--   For every $m\ge6$ there are unschedulable instances with smallest period $m$ and density at most $c(m)$. Explicitly, with $n=m+1$ and
--   $$g(m)=\frac{2(n^2-7n+2)}{5n(2n-1)(4n-1)}>0,$$
--   the following hold.
--
--   1. The instance $(m,(m+1)^{[m-2]},2m+1,4m+3,5m+5,x)$ is unschedulable for every positive integer $x$, and has smallest period $m$ and density at most $c(m)$ whenever $x\ge\lceil1/g(m)\rceil$.
--   2. $G(m)\le c(m)-g(m)<c(m)$ for all $m\ge6$.
--   3. For $m=6$ the smallest admissible $x$ is $3072$, giving $(6,7,7,7,7,13,27,35,3072)$.
--   4. For every $m\ge7$ the instance $Q_m+(x)=(m,m,(m+1)^{[m-3]},2m+2,3m+2,x)$ is unschedulable for every positive integer $x$, and
--   $$D(Q_m)=\frac2m+\frac{m-3}{m+1}+\frac1{2m+2}+\frac1{3m+2}=1-\frac{7m^2-8m-8}{2m(3m^2+5m+2)}<c(m)-g(m).$$
--   5. $G(m)\le D(Q_m)<c(m)-g(m)<c(m)$ for all $m\ge7$, and
--   $$1-G(m)\ge1-D(Q_m)=\frac7{6m}-\frac{59}{18m^2}+O(m^{-3}).$$
--   6. $Q_m+(x)$ has smallest period $m$ and density at most $c(m)$ whenever $x\ge\lceil2m(m+1)(3m+2)/(m^2-6m-4)\rceil$. For $m=7$ this is $x\ge859$, giving $(7,7,8,8,8,8,16,23,859)$.
--
--   This is the negative half of the exact range, together with the current upper bounds on $G(m)$.
--
--   **Formalization Note** The asymptotic is stated with constants $C$ and $M$ that do not depend on $m$.
--
--   Differences from the source:
--   - reading: "Explicitly, …" after "instances with smallest period $m$", without repeating the smallest period at each threshold on $x$ → `IsMinPeriod m` is stated at the threshold choices of $x$ and not for all $x\ge1$; reason: the proofs on pp. 5 and 8 show these $x$ exceed $m$; for small $x$ the list need not have minimum $m$, so the unschedulability clauses stay unconditional
--   - encoding: $O(m^{-3})$ → $\exists C,M$ with absolute remainder at most $C/m^3$ for all $m\ge M$; reason: this is the definition of the sequence asymptotic as $m\to\infty$
--   - encoding: unschedulability over ℤ in Section 2 → negation of `Schedulable`, the one-sided notion over ℕ with idle days; reason: Lemma A.1 equates the two notions for these nonempty positive integer instances, as used explicitly in the proofs on pp. 5 and 8
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Theorem 1.4, p. 2 (PDF p. 2); proofs pp. 5, 8

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP

namespace PinwheelDensity.ExactRange

/-- Theorem 1.4 (Refutation for `a₁ ≥ 6`), p. 2, all clauses and both families. The unschedulability
clauses hold for every `x ≥ 1`; the smallest period is `m` for the density-threshold choices of `x`.
`O(m⁻³)` is a uniform sequence remainder: the constants `C, M` do not depend on `m`. -/
theorem theorem_1_4 :
    (∀ m : ℕ, 6 ≤ m →
      (∃ A : List ℕ, (∀ a ∈ A, 1 ≤ a) ∧ IsMinPeriod m A ∧ density A ≤ c m ∧ ¬ Schedulable A) ∧
      0 < g m ∧
      (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (refutationP m x)) ∧
      (∀ x : ℕ, ⌈1 / g m⌉₊ ≤ x →
        IsMinPeriod m (refutationP m x) ∧ density (refutationP m x) ≤ c m) ∧
      G m ≤ ((c m - g m : ℚ) : ℝ) ∧ c m - g m < c m) ∧
    (⌈1 / g 6⌉₊ = 3072 ∧
      IsLeast {x : ℕ | 1 ≤ x ∧ density (refutationP 6 x) ≤ c 6} 3072 ∧
      refutationP 6 3072 = [6, 7, 7, 7, 7, 13, 27, 35, 3072]) ∧
    (∀ m : ℕ, 7 ≤ m →
      (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (coreQ m ++ [x])) ∧
      density (coreQ m) =
        2 / (m : ℚ) + ((m : ℚ) - 3) / ((m : ℚ) + 1) + 1 / (2 * (m : ℚ) + 2) +
          1 / (3 * (m : ℚ) + 2) ∧
      density (coreQ m) =
        1 - (7 * (m : ℚ) ^ 2 - 8 * (m : ℚ) - 8) /
          (2 * (m : ℚ) * (3 * (m : ℚ) ^ 2 + 5 * (m : ℚ) + 2)) ∧
      density (coreQ m) < c m - g m ∧
      G m ≤ ((density (coreQ m) : ℚ) : ℝ) ∧
      c m - g m < c m ∧
      1 - ((density (coreQ m) : ℚ) : ℝ) ≤ 1 - G m ∧
      (∀ x : ℕ, ⌈qThreshold m⌉₊ ≤ x →
        IsMinPeriod m (coreQ m ++ [x]) ∧ density (coreQ m ++ [x]) ≤ c m)) ∧
    (∃ (C : ℝ) (M : ℕ), ∀ m : ℕ, M ≤ m →
      |(1 - ((density (coreQ m) : ℚ) : ℝ)) - (7 / (6 * (m : ℝ)) - 59 / (18 * (m : ℝ) ^ 2))| ≤
        C / (m : ℝ) ^ 3) ∧
    (⌈qThreshold 7⌉₊ = 859 ∧ coreQ 7 ++ [859] = [7, 7, 8, 8, 8, 8, 16, 23, 859]) := by sorry

end PinwheelDensity.ExactRange
