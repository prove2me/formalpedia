-- Prove2me | Theorems.Thm_PacketFlowConv_theorem_2
-- name    : PacketFlowConv.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:44.602791+00:00
-- url     : https://prove2.me/theorems/1aace16b-ed19-4b84-b8dc-02e2c235cc6f
-- title:
--   Theorem 2, p.21 (corrected: arrival-time convergence at points where $\ell_{j,v}$ is right-continuous) — packet arrival times and cumulative flows converge to those of the flow over time
-- statement:
--   Let the instance be valid (a network, finitely many commodities on simple $o_j$-$d_j$ paths $P_j$ with integrable, bounded, boundedly supported supply rates) and $f$ a feasible flow over time along the paths. Consider the packet routings of a sequence of valid discretizations $(\alpha_n,\beta_n)$, with any tie-breaks and release orders, such that
--   $$\alpha_n\to0\qquad\text{and}\qquad\beta_n/\alpha_n\to0.$$
--   Then:
--
--   1. For every commodity $j$, node $v$ of $P_j$, particle $\varphi\in M_j=[0,m_j]$ **at which $\ell_{j,v}$ is right-continuous within $M_j$**, and $\varepsilon>0$: for all large $n$ (at which the packet $\lceil\varphi/\beta_n\rceil$ exists),
--   $$\big|\ell^D_{j,v}(\lceil\varphi/\beta_n\rceil)-\ell_{j,v}(\varphi)\big|\le\varepsilon .$$
--   2. For every arc $e$ of $P_j$, $G^+_{j,e}\to F^+_{j,e}$ and $G^-_{j,e}\to F^-_{j,e}$ uniformly on $[0,\infty)$.
--
--   This is the paper's main result: the packet routing model (a formalization of MATSim's network loading) converges to the deterministic queuing flow over time as the time step and the packet size go to zero with $\beta=o(\alpha)$.
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
--   - reading: the packet ⌈φ/β⌉ of particle φ → `max 1 ⌈φ/β⌉₊`; reason: p.14: "Particle 0 … we explicitly include it into packet 1"; for φ > 0 identical
--   - correction: (i) for every φ ∈ M_j → (i) for every φ ∈ M_j with ContinuousWithinAt (ℓ_{j,v}) [φ, m_j] φ; reason: false as printed: one arc τ = ν = 1, u = 1 on [0,1] ∪ [2,3], φ = 1, α_n = 1/n², β_n = 2/(2n³+1) give ℓ_{j,o}(1) = 1 while packet ⌈1/β_n⌉ = n³+1 has ℓ^D_{j,o} > 2 − α_n; ℓ_{j,o_j} is the left-continuous inverse of ∫u_j and ⌈φ/β⌉β → φ from the right, so the proof's "continuity of ℓ_{j,v}" holds only from the right where assumed
--   - encoding: ℓ^D_{j,v}(⌈φ/β⌉) converges → for every ε > 0, eventually in n, if the packet exists (max(1,⌈φ/β_n⌉) ≤ ⌊m_j/β_n⌋) then |ℓ^D − ℓ| ≤ ε; reason: for φ = m_j with m_j/β_n ∉ ℤ the packet ⌈φ/β_n⌉ does not exist; the guard removes only these undefined cases
--   - encoding: a sequence of discretization parameters (α, β) → a sequence `D n` of valid discretizations (α_n, β_n, tie-break, release order); reason: the same sequence; the tie-breaks may vary with n
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, Theorem 2, p.21

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_FlowOverTime

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, Theorem 2, p.21, **corrected** in (i): for a network with commodities on simple
`o_j`-`d_j`-paths with integrable, bounded, boundedly supported supply rates, every feasible flow
over time `f` along the paths, and the packet routings of a sequence of discretizations
`(α_n, β_n)` with `α_n → 0` and `β_n/α_n → 0` (any valid tie-breaks and release orders, which may
vary with `n`):

(i) for every node `v` of `P_j` and every particle `φ ∈ M_j` **at which `ℓ_{j,v}` is right-continuous
within `M_j`**, the arrival time `ℓ^D_{j,v}(⌈φ/β_n⌉)` converges to `ℓ_{j,v}(φ)`;

(ii) for every arc `e ∈ P_j`, `G⁺_{j,e} → F⁺_{j,e}` and `G⁻_{j,e} → F⁻_{j,e}` uniformly on `[0, ∞)`.

**Formalization Note.** The printed (i) (every `φ ∈ M_j`) is false: one arc `τ = ν = 1`,
`u = 1` on `[0,1] ∪ [2,3]`, `φ = 1`, `α_n = 1/n²`, `β_n = 2/(2n³+1)` give `ℓ_{j,o}(1) = 1` but
`ℓ^D_{j,o}(n³+1) > 2 − α_n`. In (i) the packet of `φ` is `max(1, ⌈φ/β_n⌉)` (p.14) and the claim is
made for the `n` at which that packet exists (`≤ ⌊m_j/β_n⌋`). -/
theorem theorem_2 {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (f : FlowOverTime E J) (hf : I.IsFeasible f)
    (D : ℕ → Discretization V E J) (hD : ∀ n, (D n).Valid)
    (hα : Filter.Tendsto (fun n => (D n).α) Filter.atTop (nhds 0))
    (hβα : Filter.Tendsto (fun n => (D n).β / (D n).α) Filter.atTop (nhds 0)) :
    (∀ (j : J) (v : V), v ∈ I.nodes j → ∀ φ ∈ Set.Icc (0 : ℝ) (I.mass j),
      ContinuousWithinAt (I.ell f j v) (Set.Icc φ (I.mass j)) φ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, (D n).packetOf φ ≤ I.nPk (D n) j →
        |I.ellD (D n) j v ((D n).packetOf φ) - I.ell f j v φ| ≤ ε) ∧
    (∀ (j : J) (e : E), e ∈ I.P j →
      TendstoUniformlyOn (fun n θ => I.Gplus (D n) j e θ) (fun θ => cum (f.fin j e) θ)
          Filter.atTop (Set.Ici 0) ∧
        TendstoUniformlyOn (fun n θ => I.Gminus (D n) j e θ) (fun θ => cum (f.fout j e) θ)
          Filter.atTop (Set.Ici 0)) := by sorry

end PacketFlowConv
