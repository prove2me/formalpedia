-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_mem_sq_of_gradAt_eq_zero_ba2ac002f700
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_mem_sq_of_gradAt_eq_zero_ba2ac002f700
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:53.433868+00:00
-- url     : https://prove2.me/theorems/c309f160-bcce-58c5-adc9-dbd5e069f355
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General mem sq of grad At eq zero ba2ac002f700: P2 M Ground Theory Heights  Heights Transverse Slice General mem sq of grad At eq zero ba2ac002f700
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General mem sq of grad At eq zero ba2ac002f700 construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General mem sq of grad At eq zero ba2ac002f700 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L40-L54

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_mem_sq_of_gradAt_eq_zero_ba2ac002f700 (q : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) (hp : eval q p = 0)
    (hg : gradAt q p = 0) : p ∈ RingHom.ker (eval q) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«mem_sq_of_gradAt_eq_zero» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_mem_sq_of_gradAt_eq_zero_ba2ac002f700
