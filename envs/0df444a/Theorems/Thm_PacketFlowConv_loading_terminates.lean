-- Prove2me | Theorems.Thm_PacketFlowConv_loading_terminates
-- name    : PacketFlowConv.loading_terminates
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:49.63878+00:00
-- url     : https://prove2.me/theorems/f913e5fe-7b3b-44bc-8422-a7d63ada8f99
-- title:
--   §2.2, p.3 — the network loading terminates: every packet leaves the last arc of its path in finite time
-- statement:
--   Let the instance be valid and let $(\alpha,\beta)$ be a valid discretization. Then every packet $i\in N_j$ of every commodity $j$ reaches its destination: there is a time step $t$ with
--   $$i\in L^-_e(t),$$
--   where $e$ is the last arc of $P_j$ (in Algorithm 2 this is the step at which $\hat c_i\leftarrow t$).
--
--   This guarantees that the minima defining the refined arrival times $\ell^D_{j,v}(i)$ are attained.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §2.2, p.3 ("Note that this happens in finite time, as packets travel along simple paths"), Algorithm 2 p.7

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, §2.2, p.3: the network loading terminates — "This alternating process is repeated
for every time step until every packet has reached its destination. Note that this happens in finite
time, as packets travel along simple paths." For every packet `i ∈ N_j` there is a time step `t` at
which it leaves the last arc of `P_j` (in Algorithm 2, `ĉ_i ← t`).

**Formalization Note.** Packets are pairs `(j, i)` with the paper's 1-based index
`1 ≤ i ≤ |N_j| = ⌊m_j/β⌋`; time steps are `t : ℕ` (the time `αt`). Any valid tie-break and release
order. -/
theorem loading_terminates {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (D : Discretization V E J) (hD : D.Valid)
    (j : J) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ I.nPk D j) (e : E) (he : I.lastArc j = some e) :
    ∃ t : ℕ, (j, i) ∈ I.Lminus D t e := by sorry

end PacketFlowConv
