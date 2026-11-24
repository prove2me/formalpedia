-- Prove2me | Theorems.Thm_PoincareFormalization_smoothConnectedSum_simplyConnected_factors
-- name    : PoincareFormalization.smoothConnectedSum_simplyConnected_factors
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T20:41:22.479806+00:00
-- url     : https://prove2.me/theorems/4bf54df9-e434-4ff1-a239-0083f1a4b8c0
-- title:
--   Factors of a simply connected smooth $3$-manifold connected sum are simply connected
-- statement:
--   Let $M$, $A$, and $B$ be closed connected smooth $3$-manifolds such that $M$ is a smooth connected sum $A \# B$. If $M$ is simply connected, then both factors $A$ and $B$ are simply connected:
--
--   $$\pi_1(M) = 1 \implies \pi_1(A) = 1 \land \pi_1(B) = 1.$$
--
--   This follows from the Seifert–van Kampen theorem applied to the open cover of $M$ by punctured copies of $A$ and $B$ overlapping along $S^2 \times \mathbb{R}$, together with invariance of $\pi_1$ under removing a point from a $3$-manifold.
--
--   **Formalization Note** The connected sum relation is `IsSmoothConnectedSum M A B`.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Theorem 1.20 (Seifert–van Kampen), p. 43; B. Kleiner and J. Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Section 81, p. 160.

import Definitions.Def_PoincareFormalization_SmoothSurgery
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

namespace PoincareFormalization

theorem smoothConnectedSum_simplyConnected_factors
    (M A B : SmoothThreeManifold) (h : IsSmoothConnectedSum M A B)
    [SimplyConnectedSpace M.Carrier] :
    SimplyConnectedSpace A.Carrier ∧ SimplyConnectedSpace B.Carrier := by
  sorry

end PoincareFormalization
