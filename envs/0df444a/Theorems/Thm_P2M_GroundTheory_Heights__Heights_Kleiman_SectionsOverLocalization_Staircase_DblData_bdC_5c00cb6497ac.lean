-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_bdC_5c00cb6497ac
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_bdC_5c00cb6497ac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:23.941416+00:00
-- url     : https://prove2.me/theorems/af9f011e-4e39-4d2e-a97e-3cf1a63c3af8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data bd C 5c00cb6497ac: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data bd C 5c00cb6497ac construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data bd C 5c00cb6497ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L240-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L240-L247

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_bdC_5c00cb6497ac (n : ℕ) (X : DblData R) (hX : X.Good) (y₀ : X.C n) : Rel (n + 1) X 0 (X.dC n y₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«Staircase».«DblData».«bdC» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_bdC_5c00cb6497ac
