-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_mul_mem_of_le_sup_sq_eb111fd8b2cf
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_mul_mem_of_le_sup_sq_eb111fd8b2cf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:17.182802+00:00
-- url     : https://prove2.me/theorems/4b47c996-9a19-4e0e-9324-bf2fee618420
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General exists mul mem of le sup sq eb111fd8b2cf: P2 M Ground Theory Heights  Heights Transverse Slice General exists mul mem of le sup sq eb111fd8
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General exists mul mem of le sup sq eb111fd8b2cf construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General exists mul mem of le sup sq eb111fd8b2cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L56-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L56-L77

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_mul_mem_of_le_sup_sq_eb111fd8b2cf (q : Fin n → ℂ) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (h : RingHom.ker (eval q) ≤ I ⊔ RingHom.ker (eval q) ^ 2) (g : MvPolynomial (Fin n) ℂ)
    (hg : eval q g = 0) : ∃ s, eval q s ≠ 0 ∧ s * g ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«exists_mul_mem_of_le_sup_sq» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_mul_mem_of_le_sup_sq_eb111fd8b2cf
