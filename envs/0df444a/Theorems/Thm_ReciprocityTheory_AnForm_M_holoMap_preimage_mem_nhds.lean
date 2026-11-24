-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holoMap_preimage_mem_nhds
-- name    : ReciprocityTheory.AnForm.M.holoMap_preimage_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:49.978831+00:00
-- url     : https://prove2.me/theorems/0a79414b-b0d6-4839-bac2-6c207b184cf6
-- title:
--   M: holo Map preimage mem nhds
-- statement:
--   The M construction uses the holo Map preimage mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Pullback.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Pullback.lean#L21-L27

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

theorem ReciprocityTheory.AnForm.M.holoMap_preimage_mem_nhds {e e' : ℕ} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {A : FinHolAtlas e' X} {B : FinHolAtlas e Y} {h : Y → X}
    (hh : HoloMap B A h) (j : Fin B.n) (k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) (hk : h ((B.chart j).symm y) ∈ (A.chart k).source) :
    (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) ∈ 𝓝 y := by sorry
