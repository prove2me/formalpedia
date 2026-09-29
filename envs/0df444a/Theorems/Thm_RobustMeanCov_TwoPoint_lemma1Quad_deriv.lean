-- Prove2me | Theorems.Thm_RobustMeanCov_TwoPoint_lemma1Quad_deriv
-- name    : RobustMeanCov.TwoPoint.lemma1Quad_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:50:09.798983+00:00
-- url     : https://prove2.me/theorems/cb2884e6-3206-492b-8aa0-d95b1efa5b15
-- title:
--   The quadratic of Lemma 1(c) has slope $q_a$ at $a$ and $q_b$ at $b$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$, let $a<b$ and $q_a,q_b\in\mathbb R$, and let $q(y)=Ay^2+By+C$ be the quadratic of Lemma 1(c). Then
--   $$
--   q'(a)=q_a\qquad\text{and}\qquad q'(b)=q_b .
--   $$
--   With $q_a=u'(a)$ and $q_b=u'(b)$ this says that $q$ meets $u$ tangentially at $a$ and $b$, which is the first observation of the paper's proof of Proposition 5.
--
--   **Formalization Note** The statement is proved for arbitrary slopes $q_a,q_b$; the paper uses it with $q_a=u'(a)$, $q_b=u'(b)$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 110, Appendix, proof of Proposition 5, right column, first sentence

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic

namespace RobustMeanCov.TwoPoint

/-- Appendix, proof of Proposition 5 (Popescu 2007, p. 110): the quadratic `q` of Lemma 1(c)
has slope `q_a` at `a` and slope `q_b` at `b`, i.e. `q'(a) = q_a` and `q'(b) = q_b`. -/
theorem lemma1Quad_deriv (u : ℝ → ℝ) (a b qa qb : ℝ) (hab : a < b) :
    deriv (lemma1Quad u a b qa qb) a = qa ∧ deriv (lemma1Quad u a b qa qb) b = qb := by sorry

end RobustMeanCov.TwoPoint
