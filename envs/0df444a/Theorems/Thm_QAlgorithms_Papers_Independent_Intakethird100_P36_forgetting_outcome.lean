-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_forgetting_outcome
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.forgetting_outcome
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:21:24.934256+00:00
-- url     : https://prove2.me/theorems/abc66826-4f88-43aa-9503-7cd3d8909791
-- title:
--   Forgetting a complete instrument’s outcome preserves monotonicity
-- statement:
--   Let \(S\) be a real-valued function on normalized finite-dimensional no-signaling assemblages, across all positive dimensions and finite nonempty alphabets. Suppose \(S\) is convex and obeys strong monotonicity for every complete Bob-to-Alice 1W-LOCC instrument: \(\sum_wp_wS(\rho_w)\le S(\rho)\), where \(p_w\) is the outcome probability and \(\rho_w=M_w(\rho)/p_w\) when \(p_w>0\); zero-probability terms contribute zero. For every such complete instrument,
--
--   $$
--   S\!\left(\sum_wM_w(\rho)\right)\le S(\rho).
--   $$
--
--   This is monotonicity of the deterministic output after the outcome is forgotten. It relates the average and unflagged versions of the resource monotonicity condition.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 5, Section V, Definition 2 and following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Section V, PDF p.5: average monotonicity plus convexity implies monotonicity
when a complete instrument's outcome is forgotten. This does not assert
monotonicity after conditioning on an arbitrary stochastic success event. -/
theorem forgetting_outcome (S : SteeringMeasure) (hmono : StrongMonotonicity S)
    (hconv : MeasureConvexity S) (P : SteeringProtocol d r s df rf sf m)
    (hcomplete : P.Complete) (rho : AssemblageBlocks d r s) (hrho : IsNormalized rho) :
    S df rf sf (protocolAction P rho) ≤ S d r s rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
