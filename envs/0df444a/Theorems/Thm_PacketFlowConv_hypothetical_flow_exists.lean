-- Prove2me | Theorems.Thm_PacketFlowConv_hypothetical_flow_exists
-- name    : PacketFlowConv.hypothetical_flow_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:12.264581+00:00
-- url     : https://prove2.me/theorems/e1e25145-4c51-44bb-a92f-81ffcfd095f5
-- title:
--   §5, p.14 (implicit) — on every arc a hypothetical flow with the packet inflow rates exists
-- statement:
--   Let the instance and the discretization be valid and $e$ an arc. Then there are outflow rates $h^-_{j,e}$ ($j\in J$), nonnegative, bounded, locally integrable and zero before $0$, such that with the inflow rates $h^+_{j,e}:=g^+_{j,e}$ the arc dynamics (3) and (4) hold on $e$ for almost all $\theta\ge0$.
--
--   The paper introduces the hypothetical flow "by setting $h^+_{j,e}:=g^+_{j,e}$ and $h^-_{j,e}$ according to (3) and (4)" without proving that such outflow rates exist; the proof of Theorem 1 needs one on every arc.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
--   - encoding: (3): f⁻_e = ν_e if z_e > 0, min{f⁺_e(θ − τ_e), ν_e} if z_e = 0 → `if 0 < z_e θ then ν_e else min (f⁺_e (θ − τ_e)) ν_e`; reason: queues are volumes; the if-then-else keeps them nonnegative and excludes no flow of the source
--   - encoding: (4) with ϑ = min { ξ ≤ θ | T_e(ξ) = θ } → (4) required for every least element ϑ of that set (`IsLeast`); reason: the minimum always exists for rates vanishing before 0, so nothing is dropped
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §5, p.14, "Hypothetical flow over time"

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_IsHypothetical

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, §5, p.14 (implicit): the hypothetical flow over time exists — "For a fixed arc
`e = uv` we introduce the hypothetical flow over time by setting `h⁺_{j,e} := g⁺_{j,e}` and
`h⁻_{j,e} : ℝ≥0 → ℝ≥0` according to (3) and (4)." For every arc there are outflow rates
`h⁻_{j,e}` (nonnegative, bounded, locally integrable, zero before `0`) satisfying (3) and (4) for the
packet inflow rates. -/
theorem hypothetical_flow_exists {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (D : Discretization V E J) (hD : D.Valid) (e : E) :
    ∃ hout : J → ℝ → ℝ, I.IsHypothetical D e hout := by sorry

end PacketFlowConv
