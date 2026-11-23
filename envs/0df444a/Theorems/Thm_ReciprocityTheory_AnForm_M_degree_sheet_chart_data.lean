-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_degree_sheet_chart_data
-- name    : ReciprocityTheory.AnForm.M.degree_sheet_chart_data
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:56.538772+00:00
-- url     : https://prove2.me/theorems/7aaa1c3e-2b32-4d30-a03f-a4d2e5b8f3cc
-- title:
--   M: degree sheet chart data
-- statement:
--   The M construction uses the degree sheet chart data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Degree.lean#L55-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Degree.lean#L55-L90

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem ReciprocityTheory.AnForm.M.degree_sheet_chart_data {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V) :
    MeasurableSet ((B.chart j) '' W) ∧
    (A.chart k ∘ h ∘ (B.chart j).symm) '' ((B.chart j) '' W) = (A.chart k) '' V ∧
    Set.InjOn (A.chart k ∘ h ∘ (B.chart j).symm) ((B.chart j) '' W) ∧
    (∀ y ∈ (B.chart j) '' W, HasFDerivWithinAt (A.chart k ∘ h ∘ (B.chart j).symm)
      ((fderiv ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y).restrictScalars ℝ) ((B.chart j) '' W) y) ∧
    (∀ y ∈ (B.chart j) '' W, h ((B.chart j).symm y) ∈ (A.chart k).source) := by sorry
