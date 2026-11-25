-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_sub_le_twist_idealSys_of_mem_3c789ee31b60
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_sub_le_twist_idealSys_of_mem_3c789ee31b60
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:11.064931+00:00
-- url     : https://prove2.me/theorems/1475531f-585a-5b0d-8348-560e37beac6e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen sub le twist ideal Sys of mem 3c789ee31b60: P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen sub le twist ideal Sys of me
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen sub le twist ideal Sys of mem 3c789ee31b60 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen sub le twist ideal Sys of mem 3c789ee31b60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L29-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubvarDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_sub_le_twist_idealSys_of_mem_3c789ee31b60 (F : SubSystem S x Ω) {pp : Ideal (Poly S N)} (I : Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (hX : (X i : Poly S N) ∈ pp) :
    F.sub I ≤ (F.twist (idealSys x pp)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«OnW».«Gen».«sub_le_twist_idealSys_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_sub_le_twist_idealSys_of_mem_3c789ee31b60
