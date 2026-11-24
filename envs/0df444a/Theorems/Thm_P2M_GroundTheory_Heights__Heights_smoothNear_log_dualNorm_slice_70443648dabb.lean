-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_log_dualNorm_slice_70443648dabb
-- name    : P2M_GroundTheory_Heights__Heights_smoothNear_log_dualNorm_slice_70443648dabb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:05.731989+00:00
-- url     : https://prove2.me/theorems/5123a618-1e0e-4954-a4c2-1a7184309088
-- title:
--   P2 M Ground Theory Heights  Heights smooth Near log dual Norm slice 70443648dabb: P2 M Ground Theory Heights  Heights smooth Near log dual Norm slice 70443648dabb
-- statement:
--   The P2 M Ground Theory Heights  Heights smooth Near log dual Norm slice 70443648dabb construction uses the P2 M Ground Theory Heights  Heights smooth Near log dual Norm slice 70443648dabb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceSectionMass.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceSectionMass.lean#L31-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceExhaustion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_smoothNear_log_dualNorm_slice_70443648dabb {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) :
    SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) fun x => Real.log (h.dualNorm x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«smoothNear_log_dualNorm_slice» := P2M_GroundTheory_Heights__Heights_smoothNear_log_dualNorm_slice_70443648dabb
