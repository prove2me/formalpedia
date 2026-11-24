-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_expansion_8e7a532e1b86
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_expansion_8e7a532e1b86
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:33.812101+00:00
-- url     : https://prove2.me/theorems/b3529880-2fea-45fc-9d4e-ca946f9eb7e4
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General exists expansion 8e7a532e1b86: P2 M Ground Theory Heights  Heights Transverse Slice General exists expansion 8e7a532e1b86
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General exists expansion 8e7a532e1b86 construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General exists expansion 8e7a532e1b86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L36-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
import Theorems.Thm_UpperTheory_Reformulated_B_Qn12_exists_expansion

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_expansion_8e7a532e1b86 (q : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    ∃ c : Fin n → MvPolynomial (Fin n) ℂ, p = C (eval q p) + ∑ i, c i * (X i - C (q i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«exists_expansion» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_exists_expansion_8e7a532e1b86
