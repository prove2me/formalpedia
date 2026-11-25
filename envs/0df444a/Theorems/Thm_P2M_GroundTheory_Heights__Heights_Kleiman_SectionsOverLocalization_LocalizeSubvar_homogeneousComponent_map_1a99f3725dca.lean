-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_homogeneousComponent_map_1a99f3725dca
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_homogeneousComponent_map_1a99f3725dca
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:26.963445+00:00
-- url     : https://prove2.me/theorems/7735d55a-a441-4eae-a310-814bc1017ad7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Localize Subvar homogeneous Component map 1a99f3725dca: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Lo
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Localize Subvar homogeneous Component map 1a99f3725dca construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Localize Subvar homogeneous Component map 1a99f3725dca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLocalizeSubvar.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLocalizeSubvar.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeSubvar
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_homogeneousComponent_map_1a99f3725dca {R A σ : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (d : ℕ) (g : MvPolynomial σ R) :
    homogeneousComponent d (map f g) = map f (homogeneousComponent d g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«LocalizeSubvar».«homogeneousComponent_map» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_homogeneousComponent_map_1a99f3725dca
