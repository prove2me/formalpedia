-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_linPoly_sub_044988d6fb10
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_linPoly_sub_044988d6fb10
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:04.431555+00:00
-- url     : https://prove2.me/theorems/93ac53ae-ed29-4f40-ae82-f2165f48df8f
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General grad At lin Poly sub 044988d6fb10: P2 M Ground Theory Heights  Heights Transverse Slice General grad At lin Poly sub 044988d6fb10
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General grad At lin Poly sub 044988d6fb10 construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General grad At lin Poly sub 044988d6fb10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L82-L85

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_linPoly_sub_044988d6fb10 (q : Fin n → ℂ) (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    gradAt q (linPoly L i - C ((L *ᵥ q) i)) = L i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«gradAt_linPoly_sub» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradAt_linPoly_sub_044988d6fb10
