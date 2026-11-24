-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_X_sub_C_65f9f86f6e98
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_X_sub_C_65f9f86f6e98
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:42.448595+00:00
-- url     : https://prove2.me/theorems/2fca48bc-4c98-44e4-a4b8-e85a82477eb5
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General grad At X sub C 65f9f86f6e98: P2 M Ground Theory Heights  Heights Transverse Slice General grad At X sub C 65f9f86f6e98
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General grad At X sub C 65f9f86f6e98 construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General grad At X sub C 65f9f86f6e98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L29-L34

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_X_sub_C_65f9f86f6e98 (q : Fin n → ℂ) (i : Fin n) (c : ℂ) :
    gradAt q (X i - C c) = Pi.single i 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«gradAt_X_sub_C» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_X_sub_C_65f9f86f6e98
