-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_theorem_b_1
-- name    : SampleCRS.AlmostGreedy.Supplement.theorem_b_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:53.17084+00:00
-- url     : https://prove2.me/theorems/6d8d5027-1bc1-4c6f-89cc-ae02fd424556
-- title:
--   Theorem B.1 — Poisson comparison for all convex and concave tests
-- statement:
--   Let $p_1,\ldots,p_n\in[0,1]$, $\lambda=\sum_i p_i$, $X\sim\operatorname{Poi}(\lambda)$ and $Y\sim\operatorname{PB}(p_1,\ldots,p_n)$. For every discrete convex function $f:\mathbb N\to\mathbb R$,
--   $$E[f(X)]\ge E[f(Y)],$$
--   and for every discrete concave $f$ the inequality is reversed. No integer-mean or positive-mean assumption is made. The finite Poisson-binomial expectation is real; the Poisson expectation may be $+\infty$ for a convex test or $-\infty$ for a concave test. Both clauses allow arbitrary growth of $f$.
--
--   The paper proves this comparison on pp.39–40 despite its attribution to Hoeffding.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: expectations of arbitrary discrete convex or concave tests → signed extended expectations in EReal and a finite real Poisson-binomial expectation; reason: finite-mean convex tests have an affine lower bound and concave tests an affine upper bound; this preserves infinite expectations without a default-zero integral
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Theorem B.1, p. 37

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_onlineKernel
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_discreteOrder
import Definitions.Def_StaticProphetSec_pbE

namespace SampleCRS.AlmostGreedy.Supplement

/-- Theorem B.1, p.37. Poisson comparison for all convex and concave tests. -/
theorem theorem_b_1 {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (f : ℕ → ℝ) :
    (DiscreteConvex f →
      (StaticProphetSec.pbE f p : EReal) ≤
        extendedE (ProbabilityTheory.poissonMeasure (Real.toNNReal (∑ i, p i))) f) ∧
    (DiscreteConcave f →
      extendedE (ProbabilityTheory.poissonMeasure (Real.toNNReal (∑ i, p i))) f ≤
        (StaticProphetSec.pbE f p : EReal)) := by sorry

end SampleCRS.AlmostGreedy.Supplement
