-- Prove2me | Theorems.Thm_PacketFlowConv_theorem_1
-- name    : PacketFlowConv.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:38.602835+00:00
-- url     : https://prove2.me/theorems/0f756dbc-f433-43d7-adab-d3ed899901c0
-- title:
--   Theorem 1, p.12 — $|\ell_{j,v}(i\beta)-\ell^D_{j,v}(i)|\le\sqrt\alpha\,C^K$ when either arrives before $K\tau^*$
-- statement:
--   Let the instance be valid and $f$ a feasible flow over time. There is a constant $C>1$ such that for every valid discretization with
--   $$\sqrt\alpha<\tau^*C^{-\lceil H/\tau^*\rceil},\qquad \beta/\alpha<1,\qquad \hat\nu_e=\nu_e\alpha/\beta\ge2\ (e\in E),\qquad \bar u_j\alpha/\beta\ge2\ (j\in J),$$
--   every commodity $j$, node $v$ of $P_j$, packet $i\in N_j$ with particle $\varphi:=i\beta$, and $K\in\mathbb N$ with $\ell_{j,v}(\varphi)<K\tau^*$ or $\ell^D_{j,v}(i)<K\tau^*$,
--   $$\big|\ell_{j,v}(\varphi)-\ell^D_{j,v}(i)\big|\le\sqrt\alpha\cdot C^K.$$
--   Here $\tau^*=\min_e\tau_e/2$ and $H$ is the time the last particle leaves the network.
--
--   Theorem 1 gives a $\sqrt\alpha$ convergence rate of the arrival times of each packet-particle pair; it is the key ingredient of Theorem 2.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
--   - reading: ℓ_{j,v} (§3.2 reuses the symbol for the earliest arrival over all paths) → the arrival time ℓ^{P_j}_{j,v} along the fixed path P_j (§3.1, p.9); reason: §4–§5 fix one simple path per commodity and the proofs use ℓ_{j,v} = T_e(ℓ_{j,u}) along P_j
--   - reading: "the flow model": the feasible flow over time of the instance → any flow f with nonnegative, bounded, locally integrable rates, zero before 0, supported on the arcs of the P_j, satisfying (2)–(4) for a.e. θ ≥ 0; reason: §4 assumes each commodity uses its single fixed path; the paper does not prove uniqueness of f, so the statement is made for every such f
--   - encoding: (3): f⁻_e = ν_e if z_e > 0, min{f⁺_e(θ − τ_e), ν_e} if z_e = 0 → `if 0 < z_e θ then ν_e else min (f⁺_e (θ − τ_e)) ν_e`; reason: queues are volumes; the if-then-else keeps them nonnegative and excludes no flow of the source
--   - encoding: (4) with ϑ = min { ξ ≤ θ | T_e(ξ) = θ } → (4) required for every least element ϑ of that set (`IsLeast`); reason: the minimum always exists for rates vanishing before 0, so nothing is dropped
--   - encoding: v ∈ V, j ∈ J_v → `v ∈ I.nodes j` (o_j followed by the heads of the arcs of P_j); reason: the same nodes
--   - reading: "C > 1 is a constant that only depends on the instance" → ∃ C > 1 after the instance and the feasible flow f; reason: the flow f is the given flow of the instance (the paper treats it as determined by the instance)
--   - encoding: α and β/α "sufficiently small" → the explicit conditions of the paragraph after the theorem (√α < τ*C^{−⌈H/τ*⌉}, β/α < 1, ν̂_e ≥ 2, ū_j α/β ≥ 2) as hypotheses; reason: the paper's own definition of "sufficiently small"
--   - encoding: H, "the time when the last particle left the network" → sup_j sup_{φ ∈ M_j} ℓ_{j,d_j}(φ); reason: the same time
--   - encoding: K ∈ ℕ = {1, 2, …} → K : ℕ (K = 0 included); reason: for K = 0 the hypothesis ℓ < 0 is never met, so nothing is added
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, Theorem 1, p.12, with the paragraph "To be more precise, …" after it

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_FlowOverTime

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, Theorem 1, p.12, with the explicit smallness conditions of the paragraph after it:
for a network with commodities on simple paths with integrable, bounded, boundedly supported supply
rates, and a feasible flow over time `f`, there is a constant `C > 1` (depending only on the
instance) such that for all `α, β` with `√α < τ* C^{−⌈H/τ*⌉}`, `β/α < 1`, `ν̂_e = ν_e α/β ≥ 2` for all
arcs and `ū_j α/β ≥ 2` for all commodities, every node `v`, every packet `i ∈ N_j` of a commodity
`j ∈ J_v` and the particle `φ := iβ`:
`|ℓ_{j,v}(φ) − ℓ^D_{j,v}(i)| ≤ √α · C^K` for `K ∈ ℕ` with `ℓ_{j,v}(φ) < Kτ*` or `ℓ^D_{j,v}(i) < Kτ*`.
Here `τ* = min_e τ_e/2` and `H` is the time the last particle left the network. -/
theorem theorem_1 {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (f : FlowOverTime E J) (hf : I.IsFeasible f) :
    ∃ C : ℝ, 1 < C ∧ ∀ D : Discretization V E J, D.Valid →
      Real.sqrt D.α < I.tauStar * (C ^ ⌈I.lastTime f / I.tauStar⌉₊)⁻¹ →
      D.β / D.α < 1 → (∀ e, 2 ≤ I.nuHat D e) → (∀ j, 2 ≤ I.supRate j * D.α / D.β) →
      ∀ (j : J) (v : V), v ∈ I.nodes j → ∀ i : ℕ, 1 ≤ i → i ≤ I.nPk D j → ∀ K : ℕ,
        (I.ell f j v ((i : ℝ) * D.β) < K * I.tauStar ∨ I.ellD D j v i < K * I.tauStar) →
        |I.ell f j v ((i : ℝ) * D.β) - I.ellD D j v i| ≤ Real.sqrt D.α * C ^ K := by sorry

end PacketFlowConv
