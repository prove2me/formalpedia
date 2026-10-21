-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_dA_dtL
-- name    : ScarceTesting.PerfectTest.dA_dtL
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:31.24701+00:00
-- url     : https://prove2.me/theorems/3d87d655-1da9-44d8-b4cd-585a55db0555
-- title:
--   Proof of Proposition 2(i), p. 23 — ∂A/∂t_L(0,1) = κ f(0)
-- statement:
--   The prior density $f$ is a nonnegative integrable function on $[0,1]$ with total mass $1$, and $F(x)=\int_0^x f$. Let $0<\kappa<1$, and assume $f$ is continuous on $[0,1]$ at $0$. The availability $A(t_L,1)=\min\{1,\kappa/(F(1)-F(t_L))\}$, as a function of $t_L$, has right derivative at $t_L=0$
--   $$\frac{\partial A}{\partial t_L}(0,1)=\kappa f(0).$$
--
--   Raising $t_L$ above $0$ removes low-prior agents from the queue, so each remaining requester is more likely to obtain a test.
--
--   **Formalization Note** The derivative is one-sided (within $[0,\infty)$), since $t_L\ge0$ for every test. Continuity of $f$ at $0$ within $[0,1]$ is what gives the value $f(0)$ of a density a meaning; the step uses exactly this.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), proof of Proposition 2 (Appendix A.1.2), part (i), p. 23, "Furthermore, ∂A/∂t_L(0,1) = κf(0)"

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Proof of Proposition 2(i), p. 23: `∂A/∂t_L(0,1) = κ f(0)` (right derivative in `t_L` at `0`,
with `t_H = 1`). -/
theorem dA_dtL (f : ℝ → ℝ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0) :
    HasDerivWithinAt (fun t => availThr f κ t 1) (κ * f 0) (Set.Ici 0) 0 := by sorry

end ScarceTesting.PerfectTest
