-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pullback_local_eq
-- name    : ReciprocityTheory.AnForm.M.pullback_local_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:37.613452+00:00
-- url     : https://prove2.me/theorems/fa263ca2-44da-4363-84d5-de0f5da4b8db
-- title:
--   M: pullback local eq
-- statement:
--   The M construction uses the pullback local eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Pullback.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Pullback.lean#L38-L47

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
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

theorem ReciprocityTheory.AnForm.M.pullback_local_eq {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h)
    (P : LocPot X) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (fun y' => P.φ (h ((B.chart j).symm y)) (h ((B.chart j).symm y'))) =ᶠ[𝓝 y]
      (P.φ (h ((B.chart j).symm y)) ∘ (A.chart k).symm) ∘
        (A.chart k ∘ h ∘ (B.chart j).symm) := by sorry
