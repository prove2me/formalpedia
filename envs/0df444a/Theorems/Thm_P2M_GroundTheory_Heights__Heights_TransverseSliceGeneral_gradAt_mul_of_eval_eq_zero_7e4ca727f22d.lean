-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_mul_of_eval_eq_zero_7e4ca727f22d
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_mul_of_eval_eq_zero_7e4ca727f22d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:26.42481+00:00
-- url     : https://prove2.me/theorems/4f39999d-536c-45b9-9bb7-a5b50785b8d4
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General grad At mul of eval eq zero 7e4ca727f22d: P2 M Ground Theory Heights  Heights Transverse Slice General grad At mul of eval eq zero 7e4ca727
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General grad At mul of eval eq zero 7e4ca727f22d construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General grad At mul of eval eq zero 7e4ca727f22d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L24-L27

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_mul_of_eval_eq_zero_7e4ca727f22d (q : Fin n → ℂ) (s g : MvPolynomial (Fin n) ℂ) (hg : eval q g = 0) :
    gradAt q (s * g) = eval q s • gradAt q g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«gradAt_mul_of_eval_eq_zero» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_mul_of_eval_eq_zero_7e4ca727f22d
