-- Prove2me | Theorems.Thm_VanderbeiLP_Networks_flow_le_cut_capacity
-- name    : VanderbeiLP.Networks.flow_le_cut_capacity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T19:07:07.318979+00:00
-- url     : https://prove2.me/theorems/fa69e8c8-f81f-40cc-bd4a-15abfc5a02e0
-- title:
--   Eq. (15.8) — flow value is at most the capacity of any cut
-- statement:
--   In the maximum-flow problem on a network $(N,A)$ with source $s$, sink $t$ and upper bounds $u_{ij}$, let $(x,x_{ts})$ be a feasible flow and $C$ a cut ($s\in C$, $t\notin C$). Then
--   $$x_{ts}\le\kappa(C)=\sum_{\substack{(i,j)\in A\\ i\in C,\ j\notin C}}u_{ij}.$$
--
--   This is the weak-duality half of the Max-Flow Min-Cut Theorem 15.1; the book obtains it from the flow-balance identity (15.7).
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 234 (PDF 245), Eq. (15.8) in the proof of Theorem 15.1

import Mathlib
import Definitions.Def_VanderbeiLP_Networks_MaxFlow

namespace VanderbeiLP.Networks

/-- **Eq. (15.8)** (Vanderbei, *Linear Programming*, 4th ed., p. 234). In the maximum-flow
problem, `x_{ts} ≤ κ(C)` for every feasible flow and every cut set `C`. -/
theorem flow_le_cut_capacity {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (s t : N)
    (x : N × N → ℝ) (xts : ℝ) (hx : IsMaxFlowFeasible A u s t x xts)
    (C : Finset N) (hC : IsCut s t C) :
    xts ≤ cutCapacity A u C := by sorry

end VanderbeiLP.Networks
