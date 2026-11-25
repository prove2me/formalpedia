-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaLinear_sqrt_det_adjoint_comp_eq_normDet_0d5987244845
-- name    : P2M_GroundTheory_Heights__Heights_AreaLinear_sqrt_det_adjoint_comp_eq_normDet_0d5987244845
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:33.66343+00:00
-- url     : https://prove2.me/theorems/23aa1896-d68d-4f7a-9290-af02c13bd4c2
-- title:
--   P2 M Ground Theory Heights  Heights Area Linear sqrt det adjoint comp eq norm Det 0d5987244845: P2 M Ground Theory Heights  Heights Area Linear sqrt det adjoint comp eq norm Det 0d5987244845
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Linear sqrt det adjoint comp eq norm Det 0d5987244845 construction uses the P2 M Ground Theory Heights  Heights Area Linear sqrt det adjoint comp eq norm Det 0d5987244845 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaLinear.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaLinear.lean#L11-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaLinear
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
open MeasureTheory Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AreaLinear_sqrt_det_adjoint_comp_eq_normDet_0d5987244845 {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    √(LinearMap.det (LinearMap.adjoint L ∘ₗ L)) = L.normDet := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaLinear».«sqrt_det_adjoint_comp_eq_normDet» := P2M_GroundTheory_Heights__Heights_AreaLinear_sqrt_det_adjoint_comp_eq_normDet_0d5987244845
