-- Prove2me | Theorems.Thm_RobustMeanCov_TwoPoint_lemma1
-- name    : RobustMeanCov.TwoPoint.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:50:40.434013+00:00
-- url     : https://prove2.me/theorems/edfe2fe9-7065-432d-83f7-bce62111689d
-- title:
--   Lemma 1: characterization of two-point support by conditions (a)–(c)
-- statement:
--   Let $u:\mathbb R\to\mathbb R$. Then $u$ has the two-point support property if and only if for every $\mu\in\mathbb R$ and every $\sigma>0$ there exist $a<b$ and $q_a,q_b\in\mathbb R$ such that
--
--   1. $(b-\mu)(\mu-a)=\sigma^2$;
--   2. $\dfrac{u(b)-u(a)}{b-a}=\dfrac{q_a+q_b}{2}$;
--   3. $q(y)=Ay^2+By+C\le u(y)$ for all $y\in\mathbb R$, where
--   $$
--   A=\frac{q_b-q_a}{2(b-a)},\quad B=\frac{bq_a-aq_b}{b-a},\quad C=\frac{bu(a)-au(b)}{b-a}-ab\,\frac{q_a-q_b}{2(b-a)} .
--   $$
--
--   The lemma turns the existence of a supporting quadratic and a two-point law into three explicit conditions on two points and two slopes; it is the tool through which Proposition 5 is proved.
--
--   **Formalization Note** No regularity is assumed on $u$, as in the paper. The two-point support property is the definition `TwoPointSupport` (Definition 1), not these conditions.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 102, Lemma 1

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_TwoPointSupport
import Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic

namespace RobustMeanCov.TwoPoint

/-- Lemma 1 (Popescu 2007, p. 102): `u` has two-point support if and only if for every `μ` and
every `σ > 0` there are `a < b` and `q_a, q_b` with
(a) `(b - μ)(μ - a) = σ²`, (b) `(u(b) - u(a)) / (b - a) = (q_a + q_b) / 2`, and
(c) the quadratic `q(y) = A y² + B y + C` with the coefficients of Lemma 1 lies below `u`. -/
theorem lemma1 (u : ℝ → ℝ) :
    TwoPointSupport u ↔
      ∀ μ σ : ℝ, 0 < σ →
        ∃ a b qa qb : ℝ, a < b ∧
          (b - μ) * (μ - a) = σ ^ 2 ∧
          (u b - u a) / (b - a) = (qa + qb) / 2 ∧
          ∀ y : ℝ, lemma1Quad u a b qa qb y ≤ u y := by sorry

end RobustMeanCov.TwoPoint
