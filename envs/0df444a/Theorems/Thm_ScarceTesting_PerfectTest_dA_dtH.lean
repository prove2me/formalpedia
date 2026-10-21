-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_dA_dtH
-- name    : ScarceTesting.PerfectTest.dA_dtH
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:37.135628+00:00
-- url     : https://prove2.me/theorems/986a28f2-4b4a-4621-bccb-6ddc4cc9aa8c
-- title:
--   Proof of Proposition 2(ii), p. 24 — ∂A/∂t_H(0,1) = −κ f(1)
-- statement:
--   The prior density $f$ is a nonnegative integrable function on $[0,1]$ with total mass $1$, and $F(x)=\int_0^x f$. Let $0<\kappa<1$, and assume $f$ is continuous on $[0,1]$ at $1$. The availability $A(0,t_H)=\min\{1,\kappa/(F(t_H)-F(0))\}$, as a function of $t_H$, has left derivative at $t_H=1$
--   $$\frac{\partial A}{\partial t_H}(0,1)=-\kappa f(1).$$
--
--   Lowering $t_H$ below $1$ removes high-prior agents from the queue and raises the availability for the others.
--
--   **Formalization Note** The derivative is one-sided (within $(-\infty,1]$), since $t_H\le1$ for every test. Continuity of $f$ at $1$ within $[0,1]$ gives $f(1)$ its meaning.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), proof of Proposition 2 (Appendix A.1.2), part (ii), p. 24, "Furthermore, ∂A/∂t_H(0,1) = −κf(1)"

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proof of Proposition 2(ii), p. 24: `∂A/∂t_H(0,1) = −κ f(1)` (left derivative in `t_H` at `1`,
with `t_L = 0`). -/
theorem dA_dtH (f : ℝ → ℝ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hf : IsPriorDensity f)
    (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1) :
    HasDerivWithinAt (fun t => availThr f κ 0 t) (-κ * f 1) (Set.Iic 1) 1 := by sorry

end ScarceTesting.PerfectTest
