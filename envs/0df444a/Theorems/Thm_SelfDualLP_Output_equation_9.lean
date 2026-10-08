-- Prove2me | Theorems.Thm_SelfDualLP_Output_equation_9
-- name    : SelfDualLP.Output.equation_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:42.546223+00:00
-- url     : https://prove2.me/theorems/07759c6e-21c2-4094-9104-ebd7696db669
-- title:
--   Equation (9) — eᵀx + eᵀs + τ + κ − (n + 1)θ = n + 1 on F_h
-- statement:
--   Work with (HLP) under the choice (7): $y^0=0$, $x^0=s^0=e$. Every feasible point $(y,x,\tau,\theta,s,\kappa)\in\mathcal F_h$ satisfies the normalizing equation
--
--   $$
--   e^Tx+e^Ts+\tau+\kappa-(n+1)\theta=n+1 .
--   $$
--
--   It is the last equality constraint of (HLP), rewritten with the definitions of the slacks $s$ and $\kappa$. Since $\theta=0$ at every optimal solution, (9) normalizes the optimal solutions; in the proof of Theorem 8 it bounds $\kappa^k$ from above.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 58, equation (9); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Equation (9) (p. 58): under the choice (7), every feasible point of (HLP) satisfies the
normalizing constraint `eᵀx + eᵀs + τ + κ − (n + 1)θ = n + 1`. -/
theorem equation_9 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : HLPFeasible7 A b c z) :
    ones n ⬝ᵥ z.x + ones n ⬝ᵥ z.s + z.τ + z.κ - ((n : ℝ) + 1) * z.θ = (n : ℝ) + 1 := by sorry
end SelfDualLP.Output
