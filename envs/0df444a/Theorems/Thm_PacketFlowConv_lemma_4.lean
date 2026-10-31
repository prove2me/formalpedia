-- Prove2me | Theorems.Thm_PacketFlowConv_lemma_4
-- name    : PacketFlowConv.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:32.814022+00:00
-- url     : https://prove2.me/theorems/daec07de-e095-4504-a6bf-003f8cd1f883
-- title:
--   Lemma 4, p.16 — $|k_{j,v}(\varphi)-\ell^D_{j,v}(\lceil\varphi/\beta\rceil)|\le C_1\sqrt\alpha+\theta C_2\sqrt\alpha$ for $k_{j,u}(\varphi)\le\theta$
-- statement:
--   There are positive constants $C_1,C_2$, depending only on $\kappa_e$ and $\nu_e$, with the following property. For every valid instance, arc $e=uv$, commodity $j\in J_e$ and time $\theta$ there is $\alpha_0>0$ such that for every valid discretization with $\alpha<\alpha_0$, $\beta/\alpha<1$, $\hat\nu_{e'}\ge2$ for all arcs and $\bar u_{j'}\alpha/\beta\ge2$ for all commodities, every hypothetical flow on $e$, and every particle $\varphi\in[0,|N_j|\beta]$ with $k_{j,u}(\varphi)\le\theta$,
--   $$\big|k_{j,v}(\varphi)-\ell^D_{j,v}(\lceil\varphi/\beta\rceil)\big|\le C_1\sqrt\alpha+\theta\,C_2\sqrt\alpha.$$
--
--   Lemma 4 compares the hypothetical flow with the packets on one arc; with Lemma 3 it gives the induction step of Theorem 1.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
--   - encoding: "α sufficiently small", "β/α sufficiently small" (standing assumptions of §5, p.12, made explicit after Theorem 1) → hypotheses β/α < 1, ν_e α/β ≥ 2 for all arcs, ū_j α/β ≥ 2 for all j, and α below a threshold α₀ (existential); reason: the paper's own conditions
--   - encoding: (3): f⁻_e = ν_e if z_e > 0, min{f⁺_e(θ − τ_e), ν_e} if z_e = 0 → `if 0 < z_e θ then ν_e else min (f⁺_e (θ − τ_e)) ν_e`; reason: queues are volumes; the if-then-else keeps them nonnegative and excludes no flow of the source
--   - encoding: (4) with ϑ = min { ξ ≤ θ | T_e(ξ) = θ } → (4) required for every least element ϑ of that set (`IsLeast`); reason: the minimum always exists for rates vanishing before 0, so nothing is dropped
--   - reading: the packet ⌈φ/β⌉ of particle φ → `max 1 ⌈φ/β⌉₊`; reason: p.14: "Particle 0 … we explicitly include it into packet 1"; for φ > 0 identical
--   - encoding: φ ∈ M_j (k_{j,u}(φ) a minimum over {H⁺_{j,e} = φ}) → 0 ≤ φ ≤ |N_j|β; reason: H⁺_{j,e} = G⁺_{j,e} takes the values [0, |N_j|β]; outside, k_{j,u}(φ) is undefined
--   - reading: C1, C2 "only depend on the instance properties κ_e and ν_e"; "for sufficiently small α" → C₁, C₂ functions of (κ_e, ν_e) chosen first; α₀ after the instance, e, j, θ; reason: the quantifier order of the statement
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, Lemma 4, p.16 (proof pp.16–20)

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_IsHypothetical

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, Lemma 4, p.16: "Given an arc `e = uv`, a point in time `θ` and a commodity
`j ∈ J_e`. For sufficiently small `α` it holds that `|k_{j,v}(φ) − ℓ^D_{j,v}(⌈φ/β⌉)| ≤ C1 · √α + θ · C2 · √α`
for `φ ∈ M_j` with `k_{j,u}(φ) ≤ θ`. Here, `C1` and `C2` are positive constants that only depend on
the instance properties `κ_e` and `ν_e`."

**Formalization Note.** `C1, C2` are positive functions of `(κ_e, ν_e)` fixed before the instance;
the threshold `α₀` may depend on the instance, `e`, `j`, `θ`. The standing assumptions of §5
(`β/α < 1`, `ν̂_e ≥ 2` for all arcs, `ū_j α/β ≥ 2`, p.12) are hypotheses. The particles are
`φ ∈ [0, |N_j|β]` (where `k_{j,u}` is defined), and particle `φ` is carried by packet
`max(1, ⌈φ/β⌉)` (p.14: particle `0` belongs to packet `1`). -/
theorem lemma_4 :
    ∃ C₁ C₂ : ℝ → ℝ → ℝ, (∀ a b, 0 < C₁ a b ∧ 0 < C₂ a b) ∧
    ∀ {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      [Fintype J] [DecidableEq J]
      (I : Instance V E J), I.Valid → ∀ (e : E) (j : J), e ∈ I.P j → ∀ θ : ℝ,
      ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ D : Discretization V E J, D.Valid → D.α < α₀ → D.β / D.α < 1 → (∀ e', 2 ≤ I.nuHat D e') →
        (∀ j', 2 ≤ I.supRate j' * D.α / D.β) →
      ∀ hout : J → ℝ → ℝ, I.IsHypothetical D e hout →
      ∀ φ : ℝ, 0 ≤ φ → φ ≤ (I.nPk D j : ℝ) * D.β → I.kU D j e φ ≤ θ →
      |kV hout j φ - I.ellD D j (I.G.head e) (D.packetOf φ)| ≤
        C₁ (I.kappa e) (I.ν e) * Real.sqrt D.α + θ * C₂ (I.kappa e) (I.ν e) * Real.sqrt D.α := by sorry

end PacketFlowConv
