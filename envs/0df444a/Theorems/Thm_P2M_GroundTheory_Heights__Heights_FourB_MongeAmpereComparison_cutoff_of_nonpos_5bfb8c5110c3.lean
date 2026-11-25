-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_nonpos_5bfb8c5110c3
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_nonpos_5bfb8c5110c3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:12.725347+00:00
-- url     : https://prove2.me/theorems/a5cf9682-d9ef-528a-9a27-6e937e2d5ad9
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of nonpos 5bfb8c5110c3: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of nonpos 5bfb8c5110c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of nonpos 5bfb8c5110c3 construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison cutoff of nonpos 5bfb8c5110c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L30-L35

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

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_nonpos_5bfb8c5110c3 {t : ℝ} (ht : t ≤ 0) : cutoff t = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«cutoff_of_nonpos» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_nonpos_5bfb8c5110c3
