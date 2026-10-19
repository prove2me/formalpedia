-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_delta_gamma_pos
-- name    : ScarceTesting.PerfectTest.delta_gamma_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:39.677088+00:00
-- url     : https://prove2.me/theorems/e4833b5f-4f92-4584-838d-ac6fbe85e8e1
-- title:
--   Proposition 2, p. 13, with δ, γ of p. 22 — if 1 > F(c) > 0 then δ = ∫_c^1 (1−µ)f > 0 and γ = ∫_0^c µf > 0
-- statement:
--   Let $0<c<1$ and let $f$ be a prior density on $[0,1]$ with distribution function $F(x)=\int_0^x f$. If there is mass on both sides of $c$, i.e. $1>F(c)>0$, then
--   $$\delta=\int_c^1(1-\mu)f(\mu)\,d\mu>0\qquad\text{and}\qquad\gamma=\int_0^c\mu f(\mu)\,d\mu>0.$$
--
--   These are the constants $\delta,\gamma>0$ whose existence Proposition 2 asserts; they enter both of its threshold conditions through $\beta\delta+\gamma$.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), Proposition 2, p. 13 ("there exist constants δ,γ > 0"), with δ and γ as defined in the proof, p. 22

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proposition 2, p. 13, with the constants of p. 22: if `1 > F(c) > 0` then
`δ = ∫_c^1 (1−μ) f(μ) dμ > 0` and `γ = ∫_0^c μ f(μ) dμ > 0`. -/
theorem delta_gamma_pos (f : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hf : IsPriorDensity f) (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1) :
    0 < deltaC f c ∧ 0 < gammaC f c := by sorry

end ScarceTesting.PerfectTest
