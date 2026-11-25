-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_exists_analytic_graph_chart
-- name    : ReciprocityTheory.AnForm.exists_analytic_graph_chart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:06.47469+00:00
-- url     : https://prove2.me/theorems/7527c8e3-c600-525f-8e34-7866443c4709
-- title:
--   An Form: exists analytic graph chart
-- statement:
--   The An Form construction uses the exists analytic graph chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L65-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L65-L138

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

theorem ReciprocityTheory.AnForm.exists_analytic_graph_chart {e c : ℕ} (f : (Fin (e + c) → ℂ) → (Fin c → ℂ))
    (p : Fin (e + c) → ℂ) (hp : f p = 0) (hf : AnalyticAt ℂ f p)
    (hsurj : Function.Surjective (fderiv ℂ f p)) :
    ∃ (σ : Equiv.Perm (Fin (e + c))) (U : Set (Fin (e + c) → ℂ)) (V : Set (Fin e → ℂ))
      (g : (Fin e → ℂ) → (Fin (e + c) → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V {x | x ∈ U ∧ f x = 0} ∧
      ∀ w ∈ V, (fun i => g w (σ (Fin.castAdd c i))) = w := by sorry
