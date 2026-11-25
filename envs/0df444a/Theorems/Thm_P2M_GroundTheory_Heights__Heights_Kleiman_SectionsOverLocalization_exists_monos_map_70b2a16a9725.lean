-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_monos_map_70b2a16a9725
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_monos_map_70b2a16a9725
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:41.337838+00:00
-- url     : https://prove2.me/theorems/044b985b-80df-4b79-b1bb-80b7015c8b7f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists monos map 70b2a16a9725: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists monos map 70b2a16a97
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists monos map 70b2a16a9725 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization exists monos map 70b2a16a9725 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L61-L71

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
omit [IsLocalization.AtPrime O 𝔪]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_monos_map_70b2a16a9725 {I : Finset (Fin (N + 1))} {s : Poly O N} (hs : s ∈ monos (S := O) I) :
    ∃ s₀ ∈ monos (S := S) I, map (algebraMap S O) s₀ = s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«exists_monos_map» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_monos_map_70b2a16a9725
