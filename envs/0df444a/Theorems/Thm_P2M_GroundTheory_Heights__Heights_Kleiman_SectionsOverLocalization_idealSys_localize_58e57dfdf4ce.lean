-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_idealSys_localize_58e57dfdf4ce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_idealSys_localize_58e57dfdf4ce
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:17.974733+00:00
-- url     : https://prove2.me/theorems/d03fec17-b540-4f80-824f-f6bd7e6b091b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization ideal Sys localize 58e57dfdf4ce: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization ideal Sys localize 58e57d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization ideal Sys localize 58e57dfdf4ce construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization ideal Sys localize 58e57dfdf4ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L157-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/MulMemSecsTwistIdealSys.lean#L157-L184

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
include 𝔪

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_idealSys_localize_58e57dfdf4ce (pp' : Ideal (Poly O N)) :
    idealSys x pp' =
      (idealSys x (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N))).baseChange O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«idealSys_localize» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_idealSys_localize_58e57dfdf4ce
