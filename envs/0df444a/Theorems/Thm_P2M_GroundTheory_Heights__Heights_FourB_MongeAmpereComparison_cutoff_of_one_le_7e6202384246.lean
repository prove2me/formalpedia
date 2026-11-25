-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_one_le_7e6202384246
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_one_le_7e6202384246
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:14.458067+00:00
-- url     : https://prove2.me/theorems/c53ef2e5-9a59-4437-9dd1-0214d648e65c
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of one le 7e6202384246: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of one le 7e6202384246
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of one le 7e6202384246 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of one le 7e6202384246 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L37-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_one_le_7e6202384246 {t : ℝ} (ht : 1 ≤ t) : cutoff t = t - (1 - cutoff 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«cutoff_of_one_le» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_one_le_7e6202384246
