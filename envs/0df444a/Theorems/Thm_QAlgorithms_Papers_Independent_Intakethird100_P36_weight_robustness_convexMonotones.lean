-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_weight_robustness_convexMonotones
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.weight_robustness_convexMonotones
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:22:54.38421+00:00
-- url     : https://prove2.me/theorems/60341fc1-3c33-48b5-ba1a-453c3e1e1ccb
-- title:
--   Steerable weight and steering robustness are convex steering monotones
-- statement:
--   For a normalized finite-dimensional no-signaling assemblage \(\rho\), define the steerable weight \(S_W(\rho)\) as the minimum of all real \(\nu\ge0\) such that \(\rho=\nu\widetilde\rho+(1-\nu)\sigma\), where \(\widetilde\rho\) is any normalized assemblage and \(\sigma\) is normalized and LHS. Define the steering robustness \(S_{\mathrm{Rob}}(\rho)\) as the minimum of all \(\nu\ge0\) for which \((\rho+\nu\widetilde\rho)/(1+\nu)\) is LHS for some normalized assemblage \(\widetilde\rho\). Both minima are attained, and
--
--   $$
--   S_W\quad\text{and}\quad S_{\mathrm{Rob}}\quad\text{are convex steering monotones}.
--   $$
--
--   Thus each is nonnegative, vanishes on LHS, is convex for every mixing coefficient in \([0,1]\), and does not increase on average under any complete Bob-to-Alice 1W-LOCC instrument. Arbitrary assemblage noise is allowed in the robustness definition. The result establishes the resource-theoretic behavior of these previously proposed measures.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 6, Theorem 3; Definitions 4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Theorem 3, PDF p.6; proof pp.11–12. Both optimizations are attained and
both quantities satisfy every clause of Definition 2. The raw weight candidates
are not artificially restricted to [0,1]. -/
theorem weight_robustness_convexMonotones :
    (∀ (d r s : ℕ) (rho : AssemblageBlocks d r s), IsNormalized rho →
      IsLeast {nu | WeightCandidate rho nu} (steerableWeight rho) ∧
      IsLeast {nu | RobustnessCandidate rho nu} (steeringRobustness rho)) ∧
    IsConvexSteeringMonotone (fun _ _ _ rho => steerableWeight rho) ∧
    IsConvexSteeringMonotone (fun _ _ _ rho => steeringRobustness rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
