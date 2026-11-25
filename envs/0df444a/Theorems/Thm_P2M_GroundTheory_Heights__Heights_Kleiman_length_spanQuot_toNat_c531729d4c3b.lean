-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_length_spanQuot_toNat_c531729d4c3b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_length_spanQuot_toNat_c531729d4c3b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:12:18.679802+00:00
-- url     : https://prove2.me/theorems/8eff333c-aaff-48d5-b8b3-cf42432f740e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman length span Quot to Nat c531729d4c3b: P2 M Ground Theory Heights  Heights Kleiman length span Quot to Nat c531729d4c3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman length span Quot to Nat c531729d4c3b construction uses the P2 M Ground Theory Heights  Heights Kleiman length span Quot to Nat c531729d4c3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L75-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen
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
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_length_spanQuot_toNat_c531729d4c3b (A B : Submodule S Ω) :
    (Module.length F (Submodule.span F (A : Set Ω) ⧸
        (Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype)).toNat =
      Module.finrank S (A ⧸ B.comap A.subtype) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«length_spanQuot_toNat» := P2M_GroundTheory_Heights__Heights_Kleiman_length_spanQuot_toNat_c531729d4c3b
