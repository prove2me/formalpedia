-- Prove2me | Theorems.Thm_ProgHedging_Convex_fixedPoint_iff_optimal
-- name    : ProgHedging.Convex.fixedPoint_iff_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:41.162985+00:00
-- url     : https://prove2.me/theorems/82145e8a-372d-43de-ab8f-161b3f47bbbd
-- title:
--   Proof of Theorem 5.1 (p. 24) — the fixed points of one exact iteration are exactly the pairs (X*, W*) with X* solving (P) and W* solving (D)
-- statement:
--   Assume the convex case and $r>0$, and let $V\in\mathcal N$, $W\in\mathcal M$. One exact iteration of progressive hedging maps $(V,W)$ to itself if and only if $V$ is an optimal solution of (P) and $W$ is an optimal solution of (D).
--
--   In the proof of Theorem 5.1 this is the identification of the zeros of $T_r$, equivalently the fixed points $Z^*=M_r(Z^*)$ of the iteration, with the primal–dual optimal pairs; combined with the convergence theory of the proximal point algorithm it gives the limits in Theorem 5.1.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 24, proof of Theorem 5.1, first paragraph and the paragraph after (5.29)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
import Definitions.Def_ProgHedging_Convex_Algorithm
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Proof of Theorem 5.1, p. 24. In the convex case with `r > 0`, a pair `(V, W) ∈ 𝒩 × ℳ` is a
fixed point of one exact iteration of the algorithm iff `V` is an optimal solution of (P) and `W` is
an optimal solution of (D). -/
theorem fixedPoint_iff_optimal {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) (V W : Policy S n)
    (hV : V ∈ pr.N) (hW : W ∈ pr.M) :
    pr.IsStep r V W V W ↔ pr.SolvesP V ∧ pr.SolvesD W := by sorry

end ProgHedging.Convex
