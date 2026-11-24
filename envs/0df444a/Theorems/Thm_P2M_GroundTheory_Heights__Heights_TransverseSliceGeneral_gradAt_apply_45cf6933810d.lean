-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_apply_45cf6933810d
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_apply_45cf6933810d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:58.046506+00:00
-- url     : https://prove2.me/theorems/69b52b9c-7606-49e8-82cf-734757f94c6f
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General grad At apply 45cf6933810d: P2 M Ground Theory Heights  Heights Transverse Slice General grad At apply 45cf6933810d
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General grad At apply 45cf6933810d construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General grad At apply 45cf6933810d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L20-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
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
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_apply_45cf6933810d (q : Fin n → ℂ) (g : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    gradAt q g j = eval q (pderiv j g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«gradAt_apply» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_apply_45cf6933810d
