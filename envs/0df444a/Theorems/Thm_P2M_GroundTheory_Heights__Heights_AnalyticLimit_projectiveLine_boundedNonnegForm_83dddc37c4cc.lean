-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_boundedNonnegForm_83dddc37c4cc
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_boundedNonnegForm_83dddc37c4cc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:18.495329+00:00
-- url     : https://prove2.me/theorems/28f0d5b2-2776-5223-958f-1ec791c4cbd9
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit projective Line bounded Nonneg Form 83dddc37c4cc: P2 M Ground Theory Heights  Heights Analytic Limit projective Line bounded Nonneg Form 83dddc37c4cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit projective Line bounded Nonneg Form 83dddc37c4cc construction uses the P2 M Ground Theory Heights  Heights Analytic Limit projective Line bounded Nonneg Form 83dddc37c4cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L229-L231

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isPlurisubharmonic
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSmoothPotential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData projLine_fubiniStudy_isPosPot)

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_boundedNonnegForm_83dddc37c4cc : IsBoundedNonnegForm p1 fsPot fsPot 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«projectiveLine_boundedNonnegForm» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_boundedNonnegForm_83dddc37c4cc
