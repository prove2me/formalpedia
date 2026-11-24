-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_up_surj_bbe98ec75402
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_up_surj_bbe98ec75402
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:18.940283+00:00
-- url     : https://prove2.me/theorems/33b9b55c-892c-4a35-a424-5a58393722d5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data up surj bbe98ec75402: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Dat
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data up surj bbe98ec75402 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data up surj bbe98ec75402 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L63-L66

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_up_surj_bbe98ec75402 (X : DblData R) (n : ℕ) (w : X.shift.C n) : ∃ z, X.up n z = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«Staircase».«DblData».«up_surj» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_up_surj_bbe98ec75402
