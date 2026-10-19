-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_proposition_2_i
-- name    : ScarceTesting.PerfectTest.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:35.887613+00:00
-- url     : https://prove2.me/theorems/04f13037-eaf9-4a74-b368-4bea99b1e5f5
-- title:
--   Proposition 2(i), p. 13 — if f(0) > (β(1−µ̄)/(βδ+γ))((1−c)/c), some (φ,1)-test with φ > 0 beats the perfect test
-- statement:
--   Let $0<c<1$, $0\le\beta<1$, and let $0<\kappa<1$ be the mass of test kits (testing resources are scarce), allocated uniformly at random among requesting agents. Let $f$ be a prior density on $[0,1]$ with distribution function $F(x)=\int_0^x f$ and mean $\bar\mu$, with mass on both sides of $c$: $1>F(c)>0$. Let $\delta=\int_c^1(1-\mu)f(\mu)\,d\mu$, $\gamma=\int_0^c\mu f(\mu)\,d\mu$, and let $S(\varphi,\sigma)$ be the planner's objective (display (9) with $\alpha=1$); a perfect test is available, so every $(\varphi,\sigma)$ with $0\le\varphi\le\sigma\le1$ can be chosen. Assume $f$ is continuous on $[0,1]$ at $0$. If
--   $$f(0)>\Big(\frac{\beta(1-\bar\mu)}{\beta\delta+\gamma}\Big)\Big(\frac{1-c}{c}\Big),$$
--   then there is a $\underline\varphi$ with $0<\underline\varphi<1$ such that
--   $$S(\underline\varphi,1)>S(0,1).$$
--
--   A small false positive rate deters low-prior agents from requesting tests, and when enough mass sits near $\mu=0$ the better allocation outweighs the extra false positives.
--
--   **Formalization Note** $\delta$ and $\gamma$ are the integrals defined on p. 22, not existentially quantified constants: with arbitrary small $\delta,\gamma$ the thresholds would exceed $f(0)$ and $f(1)$ and the statement would be empty. The value $f(0)$ (resp. $f(1)$) of a density is read with $f$ continuous on $[0,1]$ at that endpoint. $\kappa>0$ is assumed (with no kits, no test changes anything). The witness tests are kept inside the set of tests, away from the degenerate corners.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), Proposition 2(i), p. 13; proof pp. 22–23

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proposition 2(i), p. 13: with a perfect test available, scarce tests (`κ < 1`) allocated
uniformly at random, and `1 > F(c) > 0`: if `f(0) > (β(1−μ̄)/(βδ+γ))((1−c)/c)` then some
`(φ,1)`-test with `0 < φ < 1` gives `S(φ,1) > S(0,1)`. -/
theorem proposition_2_i (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1)
    (h : β * (1 - meanPrior f) / (β * deltaC f c + gammaC f c) * ((1 - c) / c) < f 0) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ S f c β κ 0 1 < S f c β κ φ 1 := by sorry

end ScarceTesting.PerfectTest
