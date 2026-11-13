-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_wasserstein_le_joint_cost
-- name    : StabilityDichotomies.Solvability.wasserstein_le_joint_cost
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:01:03.4826+00:00
-- url     : https://prove2.me/theorems/8fe6d5e8-0680-49d3-bf42-beaccba98b42
-- title:
--   Wasserstein distance is bounded by the cost of any joint law
-- statement:
--   Let $\rho$ be any joint distribution of two Boolean assignments on a finite variable set. The Wasserstein distance between the two marginal laws, with unnormalized Hamming cost, is at most the expected Hamming distance of the pair under $\rho$. This coupling upper bound is used to analyze shared randomness in the proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Section 2.3 and proof of Theorem 4.3, p.17.

import Definitions.Def_StabilityDichotomies_Solvability_Stability
noncomputable section
open scoped Classical BigOperators ENNReal

namespace StabilityDichotomies.Solvability
theorem wasserstein_le_joint_cost {V : Type} [Fintype V]
    (ρ : PMF ((V → Bool) × (V → Bool))) :
    wasserstein (ρ.map Prod.fst) (ρ.map Prod.snd) ≤
      ∑ x, ∑ y, (ρ (x,y)).toReal * hammingCost x y := by sorry
end StabilityDichotomies.Solvability
