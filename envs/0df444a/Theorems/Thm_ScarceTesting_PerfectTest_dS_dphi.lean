-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_dS_dphi
-- name    : ScarceTesting.PerfectTest.dS_dphi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:39.094211+00:00
-- url     : https://prove2.me/theorems/ed34f154-6e23-4e76-9a7e-8fc039ae3a33
-- title:
--   Proof of Proposition 2(i), p. 23 — dS/dφ(0,1) = −κβ∫_0^1(1−µ)f + (c/(1−c))κf(0)(β∫_c^1(1−µ)f + ∫_0^c µf)
-- statement:
--   Throughout, $0<c<1$ is the cost-to-benefit ratio of acting (seeking treatment). The prior density $f$ is a nonnegative integrable function on $[0,1]$ with total mass $1$, and $F(x)=\int_0^x f$. Let $0\le\beta<1$, $0<\kappa<1$, and assume $f$ is continuous on $[0,1]$ at $0$. The right derivative of $\varphi\mapsto S(\varphi,1)$ at $\varphi=0$ (the perfect test) is
--   $$\frac{dS}{d\varphi}(0,1)=-\kappa\beta\int_0^1(1-\mu)f(\mu)\,d\mu+\frac{c}{1-c}\,\kappa f(0)\Big(\beta\int_c^1(1-\mu)f(\mu)\,d\mu+\int_0^c\mu f(\mu)\,d\mu\Big).$$
--
--   The first term is the cost of the extra false positives; the second is the gain from the medium-likelihood agents who obtain tests because low-prior agents stop requesting them. Part (i) of Proposition 2 is the condition that this derivative is positive.
--
--   **Formalization Note** The derivative is one-sided (within $[0,\infty)$): false positive rates are nonnegative. $S$ is the planner's objective defined from agents' behaviour.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), proof of Proposition 2 (Appendix A.1.2), part (i), p. 23, "Using the above, we obtain: dS/dφ(0,1) = …"

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proof of Proposition 2(i), p. 23: the right derivative of `φ ↦ S(φ,1)` at `φ = 0` is
`−κβ∫_0^1 (1−μ) f + (c/(1−c)) κ f(0) (β ∫_c^1 (1−μ) f + ∫_0^c μ f)`. -/
theorem dS_dphi (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f) (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0) :
    HasDerivWithinAt (fun φ => S f c β κ φ 1)
      (-κ * β * (∫ μ in (0:ℝ)..1, (1 - μ) * f μ) +
        c / (1 - c) * κ * f 0 * (β * (∫ μ in c..1, (1 - μ) * f μ) + ∫ μ in (0:ℝ)..c, μ * f μ))
      (Set.Ici 0) 0 := by sorry

end ScarceTesting.PerfectTest
