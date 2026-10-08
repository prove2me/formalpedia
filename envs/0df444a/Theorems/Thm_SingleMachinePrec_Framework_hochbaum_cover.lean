-- Prove2me | Theorems.Thm_SingleMachinePrec_Framework_hochbaum_cover
-- name    : SingleMachinePrec.Framework.hochbaum_cover
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:49:22.714977+00:00
-- url     : https://prove2.me/theorems/e352c8fa-bca7-457f-a4d7-33c377e1117a
-- title:
--   §5, p. 659 (Hochbaum's observation) — V_1 ∪ C is a vertex cover of G^S_P when C covers G^S_P[V_{1/2}]
-- statement:
--   Let $S$ be an instance with vertex cover graph $G^S_P$, let $x$ be a half-integral feasible solution of [CS-LP] (so $x_u \in \{0,\tfrac12,1\}$, $0 \le x_u \le 1$, and $x_u + x_v \ge 1$ on every edge), and write $V_a = \{u : x_u = a\}$. If $C \subseteq V_{1/2}$ is a vertex cover of the subgraph $G^S_P[V_{1/2}]$ induced by $V_{1/2}$, then
--   $$V_1 \cup C \text{ is a vertex cover of } G^S_P.$$
--
--   The paper attributes this observation to Hochbaum; it is the step that turns a cover of the half-valued part of the LP solution into a cover of the whole graph.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 659, §5, proof of Theorem 5.1 (unnumbered; "As observed in Hochbaum [20], V_1 ∪ C gives a valid vertex cover for the graph G^S_P")

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

namespace SingleMachinePrec.Framework

/-- **Hochbaum's observation** (§5, p. 659). Let `x` be a half-integral feasible solution of
[CS-LP] and `C ⊆ V_{1/2}` a vertex cover of the subgraph `G^S_P[V_{1/2}]` induced by `V_{1/2}`.
Then `V_1 ∪ C` is a vertex cover of `G^S_P`. -/
theorem hochbaum_cover {N : Type*} [Fintype N] [DecidableEq N] (S : Instance N)
    (x : IncPair S.P → ℝ) (hx : IsCSLPFeasible S x) (hhalf : IsHalfIntegral x)
    (C : Finset (IncPair S.P)) (hCsub : C ⊆ levelSet x (1 / 2))
    (hC : ((vertexCoverGraph S.P).induce (levelSet x (1 / 2) : Set (IncPair S.P))).IsVertexCover
      {v | v.1 ∈ C}) :
    (vertexCoverGraph S.P).IsVertexCover ((levelSet x 1 ∪ C : Finset (IncPair S.P)) : Set _) := by sorry

end SingleMachinePrec.Framework
