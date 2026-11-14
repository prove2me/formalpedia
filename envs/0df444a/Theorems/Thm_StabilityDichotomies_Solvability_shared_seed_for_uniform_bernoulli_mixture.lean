-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_shared_seed_for_uniform_bernoulli_mixture
-- name    : StabilityDichotomies.Solvability.shared_seed_for_uniform_bernoulli_mixture
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:10:02.380061+00:00
-- url     : https://prove2.me/theorems/6bfc9fd9-0067-46ff-b17d-2e5f1d54e2db
-- title:
--   Shared finite seed for a uniform mixture of Bernoulli masks
-- statement:
--   For any finite number of constraint occurrences and 0 < ε ≤ 1, there is one probability distribution on Boolean masks such that every map from masks to a finite output space has the pushforward law obtained by drawing p uniformly from [1−ε,1] and retaining each occurrence independently with probability p. The same mask distribution can therefore couple any two output maps while preserving their exact mixture marginals. The result is a finite probabilistic representation and does not identify the map for a deleted multiset.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, shared-randomness argument in proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.shared_seed_for_uniform_bernoulli_mixture (m : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ ρ : PMF (Fin m → Bool), ∀ (X : Type) [Fintype X]
      (f : (Fin m → Bool) → X) (x : X),
      ((ρ.map f) x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
        ∑ mask : Fin m → Bool, retentionWeight p mask * (if f mask = x then 1 else 0) := by sorry
