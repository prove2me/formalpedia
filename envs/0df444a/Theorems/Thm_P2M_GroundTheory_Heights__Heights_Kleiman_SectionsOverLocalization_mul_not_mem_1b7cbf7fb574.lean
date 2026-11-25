-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_not_mem_1b7cbf7fb574
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_not_mem_1b7cbf7fb574
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:46.134587+00:00
-- url     : https://prove2.me/theorems/75da1b3e-47e5-4075-b17e-df6b99696a44
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul not mem 1b7cbf7fb574: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul not mem 1b7cbf7fb574
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul not mem 1b7cbf7fb574 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization mul not mem 1b7cbf7fb574 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L99-L100

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
omit [IsLocalization.AtPrime O 𝔪] [IsScalarTower S O Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_not_mem_1b7cbf7fb574 {t₁ t₂ : S} (h₁ : t₁ ∉ 𝔪) (h₂ : t₂ ∉ 𝔪) : t₁ * t₂ ∉ 𝔪 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«mul_not_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_mul_not_mem_1b7cbf7fb574
