-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_h_89c3855c6adb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_h_89c3855c6adb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:12.918342+00:00
-- url     : https://prove2.me/theorems/81423fb7-7f65-4127-a424-f87251999260
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data Good ex h 89c3855c6adb: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl D
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data Good ex h 89c3855c6adb construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data Good ex h 89c3855c6adb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L103-L107

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
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData.Good

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_h_89c3855c6adb {X : DblData R} (hX : X.Good) (p q : ℕ) {z : X.D p (q + 1)} (hz : X.h p (q + 1) z = 0) :
    ∃ w, X.h p q w = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«Staircase».«DblData».«Good».«ex_h» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ex_h_89c3855c6adb
