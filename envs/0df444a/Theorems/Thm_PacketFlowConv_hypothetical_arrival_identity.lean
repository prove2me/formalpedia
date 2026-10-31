-- Prove2me | Theorems.Thm_PacketFlowConv_hypothetical_arrival_identity
-- name    : PacketFlowConv.hypothetical_arrival_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:17.146013+00:00
-- url     : https://prove2.me/theorems/2bbbad8d-02ec-4afd-bd9d-5399be568cd4
-- title:
--   §5, p.14 — $k_{j,v}(\varphi)=k_{j,u}(\varphi)+\tau_e+q^H_e(k_{j,u}(\varphi))$
-- statement:
--   Let the instance and the discretization be valid, $e=uv$ an arc of $P_j$ and $h$ a hypothetical flow on $e$. Then for every particle $0<\varphi\le|N_j|\beta$
--   $$k_{j,v}(\varphi)=k_{j,u}(\varphi)+\tau_e+q^H_e\big(k_{j,u}(\varphi)\big).$$
--
--   The hypothetical flow follows the continuous flow dynamics, so its arrival times at $v$ are its exit times.
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
--   - encoding: particles φ (k_{j,u}(φ) is a minimum over {H⁺_{j,e} = φ}) → 0 < φ ≤ |N_j|β; reason: outside this range the minimum is over an empty set; φ = 0 uses the max-convention, which the sentence does not concern
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §5, p.14

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_IsHypothetical

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, §5, p.14: "Since the hypothetical flow on arc `e` follows the continuous flow
dynamics we have `k_{j,v}(φ) = k_{j,u}(φ) + τ_e + q^H_e(k_{j,u}(φ))`", for every particle
`φ ∈ (0, |N_j|β]` (the range of `H⁺_{j,e} = G⁺_{j,e}`, on which `k_{j,u}` is a minimum). -/
theorem hypothetical_arrival_identity {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (D : Discretization V E J) (hD : D.Valid)
    (e : E) (hout : J → ℝ → ℝ) (hH : I.IsHypothetical D e hout) (j : J) (he : e ∈ I.P j)
    (φ : ℝ) (hφ0 : 0 < φ) (hφ : φ ≤ (I.nPk D j : ℝ) * D.β) :
    kV hout j φ = I.kU D j e φ + I.τ e + I.qH D e hout (I.kU D j e φ) := by sorry

end PacketFlowConv
