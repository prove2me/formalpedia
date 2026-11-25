-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_length_eq_of_killed_42975bd4f371
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_length_eq_of_killed_42975bd4f371
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:38.643582+00:00
-- url     : https://prove2.me/theorems/a6cba167-e7db-41da-ae70-76bc51dff418
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization length eq of killed 42975bd4f371: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization length eq of killed 4297
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization length eq of killed 42975bd4f371 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization length eq of killed 42975bd4f371 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L188-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L188-L208

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
omit [IsScalarTower S O Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_length_eq_of_killed_42975bd4f371 {Q : Type*} [AddCommGroup Q] [Module O Q] [Module S Q] [IsScalarTower S O Q]
    (hkill : ∀ m ∈ 𝔪, ∀ q : Q, m • q = 0) : Module.length S Q = Module.length O Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«length_eq_of_killed» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_length_eq_of_killed_42975bd4f371
