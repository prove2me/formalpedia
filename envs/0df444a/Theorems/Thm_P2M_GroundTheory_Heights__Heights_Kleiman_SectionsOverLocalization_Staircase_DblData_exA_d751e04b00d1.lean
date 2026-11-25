-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_exA_d751e04b00d1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_exA_d751e04b00d1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:19.559803+00:00
-- url     : https://prove2.me/theorems/10efde4c-bc61-472d-aff9-0b16b7e19096
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data ex A d751e04b00d1: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data ex A d751e04b00d1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data ex A d751e04b00d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L186-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L186-L205

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
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
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_exA_d751e04b00d1 : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, X.dA n x = 0 → ∃ y, Rel n X x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«Staircase».«DblData».«exA» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_exA_d751e04b00d1
