-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_constantSystem_uT_d139ada671b2
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_constantSystem_uT_d139ada671b2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:23:20.119145+00:00
-- url     : https://prove2.me/theorems/ef1c435e-b98a-57cc-b467-8a35842e7789
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit projective Line constant System u T d139ada671b2: P2 M Ground Theory Heights  Heights Analytic Limit projective Line constant System u T d139ada671b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit projective Line constant System u T d139ada671b2 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit projective Line constant System u T d139ada671b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L195-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean#L195-L196

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_constantSystem_uT_d139ada671b2 (t : ℝ) : projectiveLineConstantSystem.uT t = fun _ => 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«projectiveLine_constantSystem_uT» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_projectiveLine_constantSystem_uT_d139ada671b2
