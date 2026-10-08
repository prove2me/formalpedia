-- Prove2me | Theorems.Thm_SelfDualLP_Regularity_equation_9
-- name    : SelfDualLP.Regularity.equation_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:32.14389+00:00
-- url     : https://prove2.me/theorems/51ed0436-36c8-448d-b487-72abb5794e6d
-- title:
--   Equation (9): normalization of the homogeneous feasible set
-- statement:
--   Under $y^0=0$ and $x^0=s^0=e$, every feasible point $(y,x,\tau,\theta,s,\kappa)$ of (HLP) satisfies
--   $$
--   e^Tx+e^Ts+\tau+\kappa-(n+1)\theta=n+1.
--   $$
--   Here $e$ is the $n$-dimensional all-ones vector, so $e^Tx$ and $e^Ts$ are sums of coordinates; $n$ may be zero.
--
--   The equality is the paper's normalization constraint written in terms of the nonnegative primal and slack fields. At an optimum with $\theta=0$, it forces at least one of $x,s,\tau,\kappa$ to be nonzero.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 58, equation (9); DOI 10.1287/moor.19.1.53

import Definitions.Def_SelfDualLP_Regularity_HLP

namespace SelfDualLP.Regularity

/-- Ye--Todd--Mizuno (1994), equation (9), p. 58. -/
theorem equation_9 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (w : HLPPoint m n)
    (hw : HLPFeasible A b c (fun _ => 1) (fun _ => 0) (fun _ => 1) w) :
    (∑ j, w.x j) + (∑ j, w.s j) + w.τ + w.κ -
      ((n : ℝ) + 1) * w.θ = (n : ℝ) + 1 := by sorry

end SelfDualLP.Regularity
