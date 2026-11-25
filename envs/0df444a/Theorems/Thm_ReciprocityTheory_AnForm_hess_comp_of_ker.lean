-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_hess_comp_of_ker
-- name    : ReciprocityTheory.AnForm.hess_comp_of_ker
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:48.374638+00:00
-- url     : https://prove2.me/theorems/f2dbb30a-e645-5f73-9759-afe144ec8088
-- title:
--   An Form: hess comp of ker
-- statement:
--   The An Form construction uses the hess comp of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L59-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L59-L98

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

theorem ReciprocityTheory.AnForm.hess_comp_of_ker {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (w b : Fin e → ℂ) (hw : fderiv ℂ τ z w = 0) :
    fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b =
      fderiv ℝ φ (τ z) (fderiv ℂ (fun x => fderiv ℂ τ x b) z w) := by sorry
