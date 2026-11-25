-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_exists_of_mem_idealMod_41f02d5bd4b2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_exists_of_mem_idealMod_41f02d5bd4b2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:34.364669+00:00
-- url     : https://prove2.me/theorems/d1adb36f-0246-424a-b8fd-b2457fd0dceb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj exists of mem ideal Mod 41f02d5bd4b2: P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj exists of mem ideal Mod 41f02d5bd4b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj exists of mem ideal Mod 41f02d5bd4b2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Mul Inj exists of mem ideal Mod 41f02d5bd4b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionMulInj.lean#L21-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionMulInj
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
open GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_exists_of_mem_idealMod_41f02d5bd4b2 (J : Ideal (Poly S N)) (I : Chart x) {z : Ω} (hz : z ∈ idealMod (x := x) J I) :
    ∃ (G m : Poly S N) (e : ℕ), G ∈ J ∧ m ∈ monos I.1 ∧ G.IsHomogeneous e ∧ m.IsHomogeneous e ∧
      z = aeval x G / aeval x m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionMulInj».«exists_of_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_exists_of_mem_idealMod_41f02d5bd4b2
