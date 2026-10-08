-- Prove2me | Theorems.Thm_VanderbeiLP_Networks_max_flow_min_cut
-- name    : VanderbeiLP.Networks.max_flow_min_cut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T19:11:59.93498+00:00
-- url     : https://prove2.me/theorems/9a7ba559-03b8-4a64-babe-cb2d1035982f
-- title:
--   Theorem 15.1 — Max-Flow Min-Cut
-- statement:
--   Let $(N,A)$ be a network with source $s$, sink $t\ne s$ and finite upper bounds $u_{ij}\ge0$ on the arcs. Then the maximum value of $x_{ts}$ over feasible flows equals the minimum value of $\kappa(C)$ over cuts $C$: there is a real number $v^*$ such that
--   $$v^*=\max\{x_{ts}: (x,x_{ts})\text{ feasible}\}=\min\{\kappa(C): s\in C,\ t\notin C\},$$
--   both the maximum and the minimum being attained.
--
--   The theorem is the network instance of LP duality and underlies the analysis of maximum-flow algorithms.
--
--   **Formalization Note** "Maximum" and "minimum" are stated with attainment (`IsGreatest`, `IsLeast`). The hypotheses $s\ne t$ and $u_{ij}\ge0$ are implicit in the book: the extra arc $(t,s)$ must not be a loop, and the upper-bounded problem $0\le x_{ij}\le u_{ij}$ is feasible only if $u_{ij}\ge0$. Connectedness is not assumed (the Chapter 14 assumption is not restated in Chapter 15, and the theorem does not need it).
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 234 (PDF 245), Theorem 15.1; setting pp. 233–234 (PDF 244–245)

import Mathlib
import Definitions.Def_VanderbeiLP_Networks_MaxFlow

namespace VanderbeiLP.Networks

/-- **Theorem 15.1, Max-Flow Min-Cut** (Vanderbei, *Linear Programming*, 4th ed., p. 234). In the
maximum-flow problem on a network `(N, A)` with source `s ≠ t` sink and finite nonnegative upper
bounds `u_{ij}`, the maximum value of `x_{ts}` over feasible flows equals the minimum value of
`κ(C)` over cuts `C`; both extrema are attained. -/
theorem max_flow_min_cut {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (hu : ∀ a ∈ A, 0 ≤ u a)
    (s t : N) (hst : s ≠ t) :
    ∃ v : ℝ,
      IsGreatest {w : ℝ | ∃ x : N × N → ℝ, IsMaxFlowFeasible A u s t x w} v ∧
      IsLeast {κ : ℝ | ∃ C : Finset N, IsCut s t C ∧ cutCapacity A u C = κ} v := by sorry

end VanderbeiLP.Networks
