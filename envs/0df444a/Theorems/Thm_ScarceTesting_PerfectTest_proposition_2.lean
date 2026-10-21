-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_proposition_2
-- name    : ScarceTesting.PerfectTest.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:36.317304+00:00
-- url     : https://prove2.me/theorems/099fdd2f-c5d3-4040-961e-a0fa8a2ae3be
-- title:
--   Proposition 2, p. 13 — scarce tests, uniform random allocation: under the density conditions at 0 / at 1, a (φ,1)- or (0,σ̄)-test beats the perfect test
-- statement:
--   Let $0<c<1$, $0\le\beta<1$, and let $0<\kappa<1$ be the mass of test kits (testing resources are scarce), allocated uniformly at random among requesting agents. Let $f$ be a prior density on $[0,1]$ with distribution function $F(x)=\int_0^x f$ and mean $\bar\mu$, with mass on both sides of $c$: $1>F(c)>0$. Let $\delta=\int_c^1(1-\mu)f(\mu)\,d\mu$, $\gamma=\int_0^c\mu f(\mu)\,d\mu$, and let $S(\varphi,\sigma)$ be the planner's objective (display (9) with $\alpha=1$); a perfect test is available, so every $(\varphi,\sigma)$ with $0\le\varphi\le\sigma\le1$ can be chosen. Assume $f$ is continuous on $[0,1]$ at $0$ and at $1$. Then $\delta>0$, $\gamma>0$, and
--
--   1. if $$f(0)>\Big(\frac{\beta(1-\bar\mu)}{\beta\delta+\gamma}\Big)\Big(\frac{1-c}{c}\Big),$$ there is a $\underline\varphi\in(0,1)$ with $S(\underline\varphi,1)>S(0,1)$;
--   2. if $$f(1)>\Big(\frac{c}{1-c}\Big)\Big(\frac{\bar\mu}{\beta\delta+\gamma}\Big),$$ there is a $\bar\sigma\in(0,1)$ with $S(0,\bar\sigma)>S(0,1)$.
--
--   When tests are scarce and handed out uniformly at random among those who ask, the perfect test need not be optimal for the planner: a slightly imperfect test changes who asks for it, and the improved allocation can outweigh the loss in accuracy.
--
--   **Formalization Note** $\delta$ and $\gamma$ are the integrals defined on p. 22, not existentially quantified constants: with arbitrary small $\delta,\gamma$ the thresholds would exceed $f(0)$ and $f(1)$ and the statement would be empty. The value $f(0)$ (resp. $f(1)$) of a density is read with $f$ continuous on $[0,1]$ at that endpoint. $\kappa>0$ is assumed (with no kits, no test changes anything). The witness tests are kept inside the set of tests, away from the degenerate corners.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), Proposition 2, p. 13; δ, γ defined on p. 22; proof pp. 22–24

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proposition 2, p. 13. Assume that a perfect test is available, that testing resources are scarce
(`0 < κ < 1`) and that allocation is uniformly random to requesting agents. For any prior density `f`
with mass on both sides of `c` (`1 > F(c) > 0`), the constants `δ = ∫_c^1 (1−μ) f` and
`γ = ∫_0^c μ f` of p. 22 are positive, and
(i) if `f(0) > (β(1−μ̄)/(βδ+γ))((1−c)/c)`, some `(φ,1)`-test with `0 < φ < 1` has `S(φ,1) > S(0,1)`;
(ii) if `f(1) > (c/(1−c))(μ̄/(βδ+γ))`, some `(0,σ)`-test with `0 < σ < 1` has `S(0,σ) > S(0,1)`. -/
theorem proposition_2 (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0) (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1) :
    0 < deltaC f c ∧ 0 < gammaC f c ∧
    (β * (1 - meanPrior f) / (β * deltaC f c + gammaC f c) * ((1 - c) / c) < f 0 →
      ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ S f c β κ 0 1 < S f c β κ φ 1) ∧
    (c / (1 - c) * (meanPrior f / (β * deltaC f c + gammaC f c)) < f 1 →
      ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ S f c β κ 0 1 < S f c β κ 0 σ) := by sorry

end ScarceTesting.PerfectTest
