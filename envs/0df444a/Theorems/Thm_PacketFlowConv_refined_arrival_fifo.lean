-- Prove2me | Theorems.Thm_PacketFlowConv_refined_arrival_fifo
-- name    : PacketFlowConv.refined_arrival_fifo
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:22.435087+00:00
-- url     : https://prove2.me/theorems/1554bf1a-1461-4a78-814e-c8f33a250849
-- title:
--   §4, p.10 — FIFO: $\ell^D_{j,v}(i)<\ell^D_{j,v}(i')$ for $i<i'$
-- statement:
--   Let the instance and the discretization be valid, $v$ a node of $P_j$ and $1\le i<i'\le|N_j|$. Then
--   $$\ell^D_{j,v}(i)<\ell^D_{j,v}(i').$$
--
--   Packets of one commodity keep their order along the path.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
--   - encoding: v ∈ V, j ∈ J_v → `v ∈ I.nodes j` (o_j followed by the heads of the arcs of P_j); reason: the same nodes
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §4, p.10

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, §4, p.10 (FIFO): "As all packets of a commodity `j` take the same path and the
arc dynamics follow the FIFO principle we have that `ℓ^D_{j,v}(i) < ℓ^D_{j,v}(i′)` for `i < i′`." -/
theorem refined_arrival_fifo {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (D : Discretization V E J) (hD : D.Valid)
    (j : J) (v : V) (hv : v ∈ I.nodes j) (i i' : ℕ) (hi1 : 1 ≤ i) (hii' : i < i')
    (hi' : i' ≤ I.nPk D j) :
    I.ellD D j v i < I.ellD D j v i' := by sorry

end PacketFlowConv
