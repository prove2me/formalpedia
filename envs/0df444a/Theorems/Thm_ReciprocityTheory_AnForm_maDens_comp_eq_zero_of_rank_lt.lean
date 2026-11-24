-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_maDens_comp_eq_zero_of_rank_lt
-- name    : ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:46.82423+00:00
-- url     : https://prove2.me/theorems/22f0d689-65ff-423e-908e-7a5de73af5ab
-- title:
--   An Form: ma Dens comp eq zero of rank lt
-- statement:
--   The An Form construction uses the ma Dens comp eq zero of rank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L127-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L127-L148

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

theorem ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt {N e : ℕ} (φ : Fin e → (Fin N → ℂ) → ℝ)
    (τ : (Fin e → ℂ) → (Fin N → ℂ)) (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z)
    (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z))
    (hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ z).toLinearMap) < e) :
    maDens (fun k => φ k ∘ τ) z = 0 := by sorry
