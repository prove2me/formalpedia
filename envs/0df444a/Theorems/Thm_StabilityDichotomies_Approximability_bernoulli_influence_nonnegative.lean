-- Prove2me | Theorems.Thm_StabilityDichotomies_Approximability_bernoulli_influence_nonnegative
-- name    : StabilityDichotomies.Approximability.bernoulli_influence_nonnegative
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:01:30.895581+00:00
-- url     : https://prove2.me/theorems/7f9ec0bc-510d-44f3-95e7-044f4974750a
-- title:
--   Nonnegativity of Bernoulli influences of a monotone potential
-- statement:
--   Let h be a monotone real-valued function of finitely many Boolean coordinates, and let 0 ≤ p ≤ 1. The sum of its Bernoulli-p expected coordinate influences is nonnegative. Each influence is the expected difference between h with that coordinate forced present and forced absent. This is the sign property needed to apply the weighted influence integral estimate in the sensitivity proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem StabilityDichotomies.Approximability.bernoulli_influence_nonnegative {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (hh : Monotone h) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ ∑ i : ι, ∑ x : ι → Bool, (∏ j : ι, if x j then p else 1-p) *
      (h (Function.update x i true) - h (Function.update x i false)) := by sorry
