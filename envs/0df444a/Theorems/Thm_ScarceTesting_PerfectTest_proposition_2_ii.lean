-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_proposition_2_ii
-- name    : ScarceTesting.PerfectTest.proposition_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:46.926349+00:00
-- url     : https://prove2.me/theorems/f26c0a8a-6faf-4276-b9bc-812640d1aeca
-- title:
--   Proposition 2(ii), p. 13 — if f(1) > (c/(1−c))(µ̄/(βδ+γ)), some (0,σ̄)-test with σ̄ < 1 beats the perfect test
-- statement:
--   Let $0<c<1$, $0\le\beta<1$, and let $0<\kappa<1$ be the mass of test kits (testing resources are scarce), allocated uniformly at random among requesting agents. Let $f$ be a prior density on $[0,1]$ with distribution function $F(x)=\int_0^x f$ and mean $\bar\mu$, with mass on both sides of $c$: $1>F(c)>0$. Let $\delta=\int_c^1(1-\mu)f(\mu)\,d\mu$, $\gamma=\int_0^c\mu f(\mu)\,d\mu$, and let $S(\varphi,\sigma)$ be the planner's objective (display (9) with $\alpha=1$); a perfect test is available, so every $(\varphi,\sigma)$ with $0\le\varphi\le\sigma\le1$ can be chosen. Assume $f$ is continuous on $[0,1]$ at $1$. If
--   $$f(1)>\Big(\frac{c}{1-c}\Big)\Big(\frac{\bar\mu}{\beta\delta+\gamma}\Big),$$
--   then there is a $\bar\sigma$ with $0<\bar\sigma<1$ such that
--   $$S(0,\bar\sigma)>S(0,1).$$
--
--   A true positive rate slightly below $1$ deters high-prior agents from requesting tests, and when enough mass sits near $\mu=1$ the tests saved for medium-likelihood agents outweigh the loss in accuracy.
--
--   **Formalization Note** $\delta$ and $\gamma$ are the integrals defined on p. 22, not existentially quantified constants: with arbitrary small $\delta,\gamma$ the thresholds would exceed $f(0)$ and $f(1)$ and the statement would be empty. The value $f(0)$ (resp. $f(1)$) of a density is read with $f$ continuous on $[0,1]$ at that endpoint. $\kappa>0$ is assumed (with no kits, no test changes anything). The witness tests are kept inside the set of tests, away from the degenerate corners.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), Proposition 2(ii), p. 13; proof pp. 23–24

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proposition 2(ii), p. 13: with a perfect test available, scarce tests (`κ < 1`) allocated
uniformly at random, and `1 > F(c) > 0`: if `f(1) > (c/(1−c))(μ̄/(βδ+γ))` then some
`(0,σ)`-test with `0 < σ < 1` gives `S(0,σ) > S(0,1)`. -/
theorem proposition_2_ii (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1)
    (h : c / (1 - c) * (meanPrior f / (β * deltaC f c + gammaC f c)) < f 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ S f c β κ 0 1 < S f c β κ 0 σ := by sorry

end ScarceTesting.PerfectTest
