-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_leviC_smul
-- name    : ReciprocityTheory.AnForm.leviC_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:32.470314+00:00
-- url     : https://prove2.me/theorems/73b0c114-f0de-5c39-90d5-928f89164a35
-- title:
--   An Form: levi C smul
-- statement:
--   The An Form construction uses the levi C smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L23-L43

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

theorem ReciprocityTheory.AnForm.leviC_smul {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin e → ℂ) :
    leviC H (c • a) b = c * leviC H a b := by sorry
