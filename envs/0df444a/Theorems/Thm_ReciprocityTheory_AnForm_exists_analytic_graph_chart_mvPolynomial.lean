-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_exists_analytic_graph_chart_mvPolynomial
-- name    : ReciprocityTheory.AnForm.exists_analytic_graph_chart_mvPolynomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:10.782802+00:00
-- url     : https://prove2.me/theorems/33cbdc11-9d1b-5db2-a550-45b27dc145c2
-- title:
--   An Form: exists analytic graph chart mv Polynomial
-- statement:
--   The An Form construction uses the exists analytic graph chart mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L180-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L180-L213

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

theorem ReciprocityTheory.AnForm.exists_analytic_graph_chart_mvPolynomial {e c : ℕ}
    (P : Fin c → MvPolynomial (Fin (e + c)) ℂ) (p : Fin (e + c) → ℂ)
    (hp : ∀ i, MvPolynomial.eval p (P i) = 0)
    (hjac : Function.Surjective (fun v : Fin (e + c) → ℂ =>
      fun i => ∑ j, MvPolynomial.eval p (MvPolynomial.pderiv j (P i)) * v j)) :
    ∃ (σ : Equiv.Perm (Fin (e + c))) (U : Set (Fin (e + c) → ℂ)) (V : Set (Fin e → ℂ))
      (g : (Fin e → ℂ) → (Fin (e + c) → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V {x | x ∈ U ∧ ∀ i, MvPolynomial.eval x (P i) = 0} ∧
      ∀ w ∈ V, (fun i => g w (σ (Fin.castAdd c i))) = w := by sorry
