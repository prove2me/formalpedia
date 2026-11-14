-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_thinning_absent_marginal
-- name    : StabilityDichotomies.Solvability.thinning_absent_marginal
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:39:55.120618+00:00
-- url     : https://prove2.me/theorems/b943e546-037c-4b7b-aefa-f6fba630cb20
-- title:
--   Exact omission probability in the thinning algorithm
-- statement:
--   Fix 0 < ε ≤ 1 and a particular constraint occurrence. Draw p uniformly from [1−ε,1] and then independently retain every occurrence with probability p. The probability that the fixed occurrence is omitted is exactly ε/2, and therefore at most ε. The formal identity integrates the finite sum of Bernoulli mask weights. This supplies the probability calculation used in the approximation part of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definition 4.2 and proof of Theorem 4.3, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.thinning_absent_marginal (m : ℕ) (i : Fin m) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε⁻¹ * ∫ p in (1 - ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask * (if mask i then 0 else 1) = ε / 2 := by sorry
