-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_hasFDerivAt_mvPolynomial_eval
-- name    : ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:19.178279+00:00
-- url     : https://prove2.me/theorems/d06fc978-825a-4b3f-b863-bb1ff2ac7ff9
-- title:
--   An Form: has FDeriv At mv Polynomial eval
-- statement:
--   The An Form construction uses the has FDeriv At mv Polynomial eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L140-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/ExistsAnalyticGraphChartMvPolynomial.lean#L140-L178

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

theorem ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval {n : ℕ} (Q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y Q)
      (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j Q) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) x := by sorry
