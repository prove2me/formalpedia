-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_hessC_eq_leviC
-- name    : ReciprocityTheory.AnForm.hessC_eq_leviC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:59.995779+00:00
-- url     : https://prove2.me/theorems/f4cf28d7-47e0-4fc4-804b-a3dcbb35880f
-- title:
--   An Form: hess C eq levi C
-- statement:
--   The An Form construction uses the hess C eq levi C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L13-L14

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Complex Filter Topology
open scoped Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.hessC_eq_leviC {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (i j : Fin e) :
    hessC f z i j = leviC (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := by sorry
