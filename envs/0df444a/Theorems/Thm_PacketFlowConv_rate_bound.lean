-- Prove2me | Theorems.Thm_PacketFlowConv_rate_bound
-- name    : PacketFlowConv.rate_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:58.233881+00:00
-- url     : https://prove2.me/theorems/31573406-5fa8-4838-b04d-37434195f1b2
-- title:
--   §5, p.12 — $\kappa_e$ bounds the in- and outflow rates of $e$ in both models when $\beta/\alpha<1$
-- statement:
--   Let the instance and the discretization be valid with $\beta/\alpha<1$, let $f$ be a feasible flow over time and $e$ an arc. Then
--
--   1. in the packet model, $g^+_e(\theta)\le\kappa_e$ and $g^-_e(\theta)\le\kappa_e$ for all $\theta\ge0$;
--   2. in the flow over time, $f^+_e(\theta)\le\kappa_e$ and $f^-_e(\theta)\le\kappa_e$ for almost all $\theta\ge0$.
--
--   The paper states this after defining $\kappa_e$: each predecessor arc $e'$ (including the auxiliary arcs of capacity $\bar u_j$ for released packets) sends at most $\hat\nu_{e'}+1$ packets per step. The bound is used throughout §5 as the maximal slope of the cumulative flows.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
--   - reading: "the flow model": the feasible flow over time of the instance → any flow f with nonnegative, bounded, locally integrable rates, zero before 0, supported on the arcs of the P_j, satisfying (2)–(4) for a.e. θ ≥ 0; reason: §4 assumes each commodity uses its single fixed path; the paper does not prove uniqueness of f, so the statement is made for every such f
--   - encoding: (3): f⁻_e = ν_e if z_e > 0, min{f⁺_e(θ − τ_e), ν_e} if z_e = 0 → `if 0 < z_e θ then ν_e else min (f⁺_e (θ − τ_e)) ν_e`; reason: queues are volumes; the if-then-else keeps them nonnegative and excludes no flow of the source
--   - encoding: (4) with ϑ = min { ξ ≤ θ | T_e(ξ) = θ } → (4) required for every least element ϑ of that set (`IsLeast`); reason: the minimum always exists for rates vanishing before 0, so nothing is dropped
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §5, p.12, paragraph after the definition of κ_e

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_FlowOverTime

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, §5, p.12 (the rate bound `κ_e`): "Since the number of leaving packets of each
predecessor arc `e′` (including the auxiliary arcs for newly released packets) is upper bounded by
`ν̂_{e′} + 1` in every time step, we have that `g⁻_{e′}(θ) ≤ ν_{e′} + β/α`. Since `β/α` is assumed
to be smaller than 1, `κ_e` does indeed bound the maximal inflow into `e` as well as the maximal
outflow of `e` for both the packet model as well as the flow over time model."

Under `β/α < 1`: `g⁺_e(θ), g⁻_e(θ) ≤ κ_e` for all `θ ≥ 0`, and for every feasible flow over time
`f⁺_e(θ), f⁻_e(θ) ≤ κ_e` for almost all `θ ≥ 0`. -/
theorem rate_bound {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (D : Discretization V E J) (hD : D.Valid)
    (hβα : D.β / D.α < 1) (f : FlowOverTime E J) (hf : I.IsFeasible f) (e : E) :
    (∀ θ : ℝ, 0 ≤ θ → I.gPlusTot D e θ ≤ I.kappa e ∧ I.gMinusTot D e θ ≤ I.kappa e) ∧
    (∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
      tot (fun j => f.fin j e) θ ≤ I.kappa e ∧ tot (fun j => f.fout j e) θ ≤ I.kappa e) := by sorry

end PacketFlowConv
