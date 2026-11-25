-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_vecMul_hessC_comp_eq_zero
-- name    : ReciprocityTheory.AnForm.vecMul_hessC_comp_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:29.538141+00:00
-- url     : https://prove2.me/theorems/a185d816-751b-48be-8f23-06491f454e5a
-- title:
--   An Form: vec Mul hess C comp eq zero
-- statement:
--   The An Form construction uses the vec Mul hess C comp eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L100-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean#L100-L125

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

theorem ReciprocityTheory.AnForm.vecMul_hessC_comp_eq_zero {N e : ℕ} (φ : (Fin N → ℂ) → ℝ) (τ : (Fin e → ℂ) → (Fin N → ℂ))
    (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z))
    (v : Fin e → ℂ) (hv : fderiv ℂ τ z v = 0) :
    v ᵥ* hessC (φ ∘ τ) z = 0 := by sorry
