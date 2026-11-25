-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_inv_algebraMap_079c35648306
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_inv_algebraMap_079c35648306
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:21.714799+00:00
-- url     : https://prove2.me/theorems/eb66dc33-6c28-4521-925a-c1d88c0fdd60
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists inv algebra Map 079c35648306: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists inv algebra Ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists inv algebra Map 079c35648306 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists inv algebra Map 079c35648306 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L148-L153

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_inv_algebraMap_079c35648306 {t : S} (ht : t ∉ 𝔪) : ∃ u : O, algebraMap O Ω u * algebraMap S Ω t = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_inv_algebraMap» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_inv_algebraMap_079c35648306
