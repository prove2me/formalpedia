-- Prove2me | Theorems.Thm_PacketFlowConv_lemma_1
-- name    : PacketFlowConv.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:30.616992+00:00
-- url     : https://prove2.me/theorems/240fb8e4-28ee-4124-9740-9b58910a35e7
-- title:
--   Lemma 1, p.11 — a packet entering $e=uv$ at refined time $\ell^D_{j,u}(i)$ leaves at $T^D_{j,e}(\ell^D_{j,u}(i))$
-- statement:
--   Let the instance and the discretization be valid, $e=uv$ an arc of $P_j$ and $i\in N_j$. Then
--   $$\ell^D_{j,v}(i)=T^D_{j,e}\big(\ell^D_{j,u}(i)\big),$$
--   where $T^D_{j,e}(\theta)=\theta+\lceil\tau_e\rceil_\alpha+q^D_{j,e}(\theta)$ is the exit time of the packet model.
--
--   This is the packet-model analogue of $\ell_{j,v}=T_e(\ell_{j,u})$ in the flow over time.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, Lemma 1, p.11

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, Lemma 1, p.11: "If packet `i ∈ N_j` enters `e = uv` at refined time
`ℓ^D_{j,u}(i) ∈ ℝ≥0`, it leaves `e` at refined time `ℓ^D_{j,v}(i) = T^D_{j,e}(ℓ^D_{j,u}(i))`." -/
theorem lemma_1 {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (D : Discretization V E J) (hD : D.Valid)
    (j : J) (e : E) (he : e ∈ I.P j) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ I.nPk D j) :
    I.ellD D j (I.G.head e) i = I.TD D j e (I.ellD D j (I.G.tail e) i) := by sorry

end PacketFlowConv
