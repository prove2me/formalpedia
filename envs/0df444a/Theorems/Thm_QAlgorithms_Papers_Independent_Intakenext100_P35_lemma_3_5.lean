-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_lemma_3_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.lemma_3_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:14:36.230995+00:00
-- url     : https://prove2.me/theorems/697aa98d-7340-4bf5-bc6b-e3a6eee193f6
-- title:
--   Lemma 3.5
-- statement:
--   Let $(f_k)$ be bounded in $\mathcal B$, converge pointwise on $\mathbb C_+$ to $f$, and satisfy, for every $r>0$, uniform-in-$k$ vanishing as $\delta\downarrow0$ of $\int_0^\delta\sup_{|\beta|\le r}|f_k'(\alpha+i\beta)|\,d\alpha$. If $g\in\mathcal B$ vanishes as $|z|\to\infty$ in the half-plane, then
--
--   $$f\in\mathcal B,\qquad\|(f_k-f)g\|_{\mathcal B}\longrightarrow0.$$
--
--   The localized derivative condition gives the norm approximation needed for strong calculus convergence.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 8, Lemma 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Lemma 3.5, arXiv:2202.03143v1, PDF page(s) 8, 9. -/
theorem lemma_3_5
(fs : ℕ → AnalyticSymbol) (f g : AnalyticSymbol) (hfs : BConvergence fs f)
(hg : BesovClass g) (hvanish : Vanishes g) :
    BesovClass f ∧ NormConverges bSize (fun n => (fs n - f) * g) 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
