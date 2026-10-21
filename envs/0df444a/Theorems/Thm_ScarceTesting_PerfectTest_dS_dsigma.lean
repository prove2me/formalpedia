-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_dS_dsigma
-- name    : ScarceTesting.PerfectTest.dS_dsigma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:43.877201+00:00
-- url     : https://prove2.me/theorems/8907abbb-f01c-4a93-b3d2-6ff1912a40c5
-- title:
--   Proof of Proposition 2(ii), p. 24 — dS/dσ(0,1) = −κf(1)((1−c)/c)(β∫_c^1(1−µ)f + ∫_0^c µf) + κµ̄ (printed middle term corrected)
-- statement:
--   Let $0<c<1$, $0\le\beta<1$, $0<\kappa<1$, let $f$ be a prior density on $[0,1]$, continuous on $[0,1]$ at $1$, and let $S$ be the planner's objective. The left derivative of $\sigma\mapsto S(0,\sigma)$ at $\sigma=1$ (the perfect test) is
--   $$\frac{dS}{d\sigma}(0,1)=-\kappa f(1)\frac{1-c}{c}\,\beta\int_c^1(1-\mu)f(\mu)\,d\mu+\kappa\int_0^1\mu f(\mu)\,d\mu-\kappa f(1)\frac{1-c}{c}\int_0^c\mu f(\mu)\,d\mu.$$
--
--   The middle term is the loss in detected infections from the lower true positive rate; the other two are the gain from high-prior agents leaving the queue. Part (ii) of Proposition 2 is the condition that this derivative is negative.
--
--   **Formalization Note** The page prints the middle term as $\kappa\int_0^c\mu f(\mu)\,d\mu$. Differentiating $S(0,\sigma)=\dots+\int_c^{t_H}A\big((1-\mu)\beta-\mu(1-\sigma)\big)dF+\int_0^cA\,\mu\sigma\,dF$ in $\sigma$ produces $\kappa\int_c^1\mu f$ from the first integral and $\kappa\int_0^c\mu f$ from the second, so the middle term is $\kappa\int_0^1\mu f=\kappa\bar\mu$; the condition on $f(1)$ that the page derives next (with $\int_0^1\mu f$ in its numerator) is the one this corrected derivative gives. The derivative is one-sided (within $(-\infty,1]$): true positive rates are at most $1$.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), proof of Proposition 2 (Appendix A.1.2), part (ii), p. 24, "Using the above, we obtain dS/dσ(0,1) = …" (middle term corrected)

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proof of Proposition 2(ii), p. 24, corrected: the left derivative of `σ ↦ S(0,σ)` at `σ = 1` is
`−κ f(1) ((1−c)/c) β ∫_c^1 (1−μ) f + κ ∫_0^1 μ f − κ f(1) ((1−c)/c) ∫_0^c μ f`.
The printed display has `κ ∫_0^c μ f` as its middle term; differentiating the factor `−μ(1−σ)` of the
integral over `[c, t_H]` contributes `κ ∫_c^1 μ f` as well, so the middle term is `κ ∫_0^1 μ f = κ μ̄`,
which is the term the printed condition on `f(1)` uses. -/
theorem dS_dsigma (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f) (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1) :
    HasDerivWithinAt (fun σ => S f c β κ 0 σ)
      (-κ * f 1 * ((1 - c) / c) * β * (∫ μ in c..1, (1 - μ) * f μ) +
        κ * (∫ μ in (0:ℝ)..1, μ * f μ) -
        κ * f 1 * ((1 - c) / c) * (∫ μ in (0:ℝ)..c, μ * f μ))
      (Set.Iic 1) 1 := by sorry

end ScarceTesting.PerfectTest
