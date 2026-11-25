-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradSpace_sliceIdeal_d192009989c4
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradSpace_sliceIdeal_d192009989c4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:31.892631+00:00
-- url     : https://prove2.me/theorems/fb1d8cb8-143f-49ac-87d2-65294c1d9c02
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General grad Space slice Ideal d192009989c4: P2 M Ground Theory Heights  Heights Transverse Slice General grad Space slice Ideal d192009989c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General grad Space slice Ideal d192009989c4 construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General grad Space slice Ideal d192009989c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L87-L105

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradSpace_sliceIdeal_d192009989c4 (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) :
    gradSpace (sliceIdeal W L q) q = gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«gradSpace_sliceIdeal» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_gradSpace_sliceIdeal_d192009989c4
