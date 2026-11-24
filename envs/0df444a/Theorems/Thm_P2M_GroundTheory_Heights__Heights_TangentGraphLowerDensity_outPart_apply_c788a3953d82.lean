-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_outPart_apply_c788a3953d82
-- name    : P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_outPart_apply_c788a3953d82
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:49.728895+00:00
-- url     : https://prove2.me/theorems/b1448d5e-2e8e-41f3-9108-016b264036b4
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Graph Lower Density out Part apply c788a3953d82: P2 M Ground Theory Heights  Heights Tangent Graph Lower Density out Part apply c788a3953d82
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Graph Lower Density out Part apply c788a3953d82 construction uses the P2 M Ground Theory Heights  Heights Tangent Graph Lower Density out Part apply c788a3953d82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L29-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTangentGraphLowerDensity
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
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_outPart_apply_c788a3953d82 {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : {j : Fin n // j ∉ I}) :
    TangentGraphLowerDensity.outPart b I z j = inner ℂ (b j) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentGraphLowerDensity».«outPart_apply» := P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_outPart_apply_c788a3953d82
