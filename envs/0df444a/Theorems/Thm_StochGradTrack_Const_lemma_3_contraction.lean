-- Prove2me | Theorems.Thm_StochGradTrack_Const_lemma_3_contraction
-- name    : StochGradTrack.Const.lemma_3_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:36.201273+00:00
-- url     : https://prove2.me/theorems/85572306-0325-4ccd-8df1-50e3abc910aa
-- title:
--   Lemma 3, p. 420 — for 0 < α < 2/(μ + L), ‖x − α∇f(x) − x*‖ ≤ (1 − αμ)‖x − x*‖
-- statement:
--   Let $n\ge1$, let each $f_i$ satisfy Assumption 2 (gradient $\nabla f_i$, $\mu$-strongly convex, $L$-smooth, $p\ge1$) and let $x^*$ minimize $f=\frac1n\sum_i f_i$. If $0<\alpha<\frac{2}{\mu+L}$, then for every $x\in\mathbb R^p$
--   $$\|x-\alpha\nabla f(x)-x^*\|\le(1-\alpha\mu)\|x-x^*\| .$$
--
--   A gradient step of the averaged objective is a contraction towards $x^*$ with factor $1-\alpha\mu$; this produces the $(1-\alpha\mu)$ entry of the linear system (21).
--
--   **Formalization Note.** $n\ge1$ (the agent set is nonempty) and $\alpha>0$ (the standing "$\alpha>0$ is a constant stepsize", p. 415) are explicit. The paper cites [46, Lemma 10] for the proof.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Lemma 3, second statement, p. 420

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem lemma_3_contraction {n p : ℕ} (hn : 0 < n) (f : Fin n → E p → ℝ)
    (gradf : Fin n → E p → E p) (μ L : ℝ) (h2 : Assumption2 f gradf μ L) (xstar : E p)
    (hopt : IsMinimizer f xstar) (α : ℝ) (hα : 0 < α) (hαμL : α < 2 / (μ + L)) :
    ∀ x : E p, ‖x - α • gradAvg gradf x - xstar‖ ≤ (1 - α * μ) * ‖x - xstar‖ := by sorry

end StochGradTrack.Const
