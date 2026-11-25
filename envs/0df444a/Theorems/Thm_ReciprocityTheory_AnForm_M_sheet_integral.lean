-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_sheet_integral
-- name    : ReciprocityTheory.AnForm.M.sheet_integral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:30.985738+00:00
-- url     : https://prove2.me/theorems/7077b4be-f9d7-4639-a26d-eaf542db0ddb
-- title:
--   M: sheet integral
-- statement:
--   The M construction uses the sheet integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Degree.lean#L92-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Degree.lean#L92-L122

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

theorem ReciprocityTheory.AnForm.M.sheet_integral {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (j : Fin B.n) (k : Fin A.n) {W : Set Y} {V : Set X} (hW : IsOpen W)
    (hWj : W ⊆ (B.chart j).source) (hVk : V ⊆ (A.chart k).source) (hbij : Set.BijOn h W V)
    (f : X → ℝ) :
    (IntegrableOn (fun y => f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y) ((B.chart j) '' W) ↔
      IntegrableOn (fun z => f ((A.chart k).symm z) * locDens A Φ k z) ((A.chart k) '' V)) ∧
    ∫ y in (B.chart j) '' W, f (h ((B.chart j).symm y)) *
        locDens B (fun i => (Φ i).pullback h hh.1) j y =
      ∫ z in (A.chart k) '' V, f ((A.chart k).symm z) * locDens A Φ k z := by sorry
