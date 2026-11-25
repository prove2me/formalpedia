-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_chartRing_54282771e4c4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_chartRing_54282771e4c4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:46.518849+00:00
-- url     : https://prove2.me/theorems/3f57b319-247a-4b8e-b185-45a51f3aae46
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem chart Ring 54282771e4c4: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem cha
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem chart Ring 54282771e4c4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists mul mem chart Ring 54282771e4c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L91-L95

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_chartRing_54282771e4c4 {I : Chart x} {a : Ω} (ha : a ∈ chartRing O x I) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * a ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_mul_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mul_mem_chartRing_54282771e4c4
