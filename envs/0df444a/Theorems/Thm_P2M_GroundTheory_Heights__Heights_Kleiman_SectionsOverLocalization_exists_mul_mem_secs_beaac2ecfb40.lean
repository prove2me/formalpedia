-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_secs_beaac2ecfb40
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_secs_beaac2ecfb40
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:50.485814+00:00
-- url     : https://prove2.me/theorems/00401ff9-624b-42b0-bf0e-0102c4a8db42
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem secs beaac2ecfb40: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem secs beaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem secs beaac2ecfb40 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem secs beaac2ecfb40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L136-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L136-L146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_secs_beaac2ecfb40 {G : SubSystem S x Ω} {z : Ω} (hz : z ∈ (G.baseChange O).secs) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * z ∈ G.secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_mul_mem_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_secs_beaac2ecfb40
