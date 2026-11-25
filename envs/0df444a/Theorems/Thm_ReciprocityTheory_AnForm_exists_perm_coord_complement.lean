-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_exists_perm_coord_complement
-- name    : ReciprocityTheory.AnForm.exists_perm_coord_complement
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:19.535614+00:00
-- url     : https://prove2.me/theorems/45fcc372-a5c8-577f-967e-2b27f15be059
-- title:
--   An Form: exists perm coord complement
-- statement:
--   The An Form construction uses the exists perm coord complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L7-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L7-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Function

theorem ReciprocityTheory.AnForm.exists_perm_coord_complement {e c : ℕ} (A : (Fin (e + c) → ℂ) →ₗ[ℂ] (Fin c → ℂ))
    (hA : Surjective A) :
    ∃ σ : Equiv.Perm (Fin (e + c)),
      ∀ v, (∀ i : Fin e, v (σ (Fin.castAdd c i)) = 0) → A v = 0 → v = 0 := by sorry
