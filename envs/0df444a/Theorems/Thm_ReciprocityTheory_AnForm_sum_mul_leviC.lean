-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_sum_mul_leviC
-- name    : ReciprocityTheory.AnForm.sum_mul_leviC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:13.971066+00:00
-- url     : https://prove2.me/theorems/8699c072-b26e-440a-a5f2-989f77f64f31
-- title:
--   An Form: sum mul levi C
-- statement:
--   The An Form construction uses the sum mul levi C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L45-L57

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

theorem ReciprocityTheory.AnForm.sum_mul_leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (v b : Fin e → ℂ) :
    ∑ i, v i * leviC H (Pi.single i 1) b = leviC H v b := by sorry
