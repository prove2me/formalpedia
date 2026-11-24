-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ha0_aefa022df884
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ha0_aefa022df884
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:55.818684+00:00
-- url     : https://prove2.me/theorems/f486fb77-e5d0-4e83-9aaa-84b2f0881399
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data Good ha0 aefa022df884: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Da
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data Good ha0 aefa022df884 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Staircase Dbl Data Good ha0 aefa022df884 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean#L120-L123

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ha0_aefa022df884 {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) : X.h p 0 (X.a p x) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«Staircase».«DblData».«Good».«ha0» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ha0_aefa022df884
