-- Prove2me | Theorems.Thm_RobustMeanCov_TwoPoint_lemma1Quad_eq_of_chord
-- name    : RobustMeanCov.TwoPoint.lemma1Quad_eq_of_chord
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:49:36.1008+00:00
-- url     : https://prove2.me/theorems/2f101a6f-d00c-4267-9642-576796b85d2e
-- title:
--   Proof of Lemma 1: under condition (b) the quadratic of Lemma 1(c) meets $u$ at $a$ and $b$
-- statement:
--   Let $u:\mathbb R\to\mathbb R$, let $a<b$ and $q_a,q_b\in\mathbb R$, and let $q(y)=Ay^2+By+C$ be the quadratic of Lemma 1(c). If condition (b) of Lemma 1 holds,
--   $$
--   \frac{u(b)-u(a)}{b-a}=\frac{q_a+q_b}{2},
--   $$
--   then
--   $$
--   q(a)=u(a)\qquad\text{and}\qquad q(b)=u(b).
--   $$
--
--   This is the first step of the proof of Lemma 1: combined with (c), the quadratic supports $u$ and touches it at the two points $a,b$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 102, proof of Lemma 1, first sentence

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic

namespace RobustMeanCov.TwoPoint

/-- Proof of Lemma 1 (Popescu 2007, p. 102), first sentence: if `a < b` and condition (b)
`(u(b) - u(a)) / (b - a) = (q_a + q_b) / 2` holds, the quadratic `q` of Lemma 1(c) satisfies
`q(a) = u(a)` and `q(b) = u(b)`. -/
theorem lemma1Quad_eq_of_chord (u : ℝ → ℝ) (a b qa qb : ℝ) (hab : a < b)
    (hchord : (u b - u a) / (b - a) = (qa + qb) / 2) :
    lemma1Quad u a b qa qb a = u a ∧ lemma1Quad u a b qa qb b = u b := by sorry

end RobustMeanCov.TwoPoint
