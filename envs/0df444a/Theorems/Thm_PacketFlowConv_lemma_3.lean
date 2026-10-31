-- Prove2me | Theorems.Thm_PacketFlowConv_lemma_3
-- name    : PacketFlowConv.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:14.492772+00:00
-- url     : https://prove2.me/theorems/5fd4fb61-11dd-48cb-93e4-8b15f06a7342
-- title:
--   Lemma 3, p.14 — closeness at $u$ of all earlier particles gives $|\ell_{j,v}(\varphi)-k_{j,v}(\varphi)|\le11\kappa_e\delta/\nu_e$
-- statement:
--   Fix a valid instance, a feasible flow over time $f$, a valid discretization with $\beta/\alpha<1$ and $\hat\nu_{e'}\ge2$ for all arcs (p.20: "The last two conditions are needed for Lemma 3"), an arc $e=uv$ of $P_j$, a hypothetical flow $h$ on $e$, a packet $i\in N_j$ with particle $\varphi=i\beta$, and $\delta>\alpha$ such that
--   $$|\ell_{j',u}(\phi)-k_{j',u}(\phi)|\le\delta$$
--   for all $j'\in J_e$ and all particles $\phi=i'\beta\in M_{j'}$, $i'\ge1$, with $\ell_{j',u}(\phi)\le\ell_{j,u}(\varphi)$ or $k_{j',u}(\phi)\le k_{j,u}(\varphi)$.
--
--   Then
--   $$|\ell_{j,v}(\varphi)-k_{j,v}(\varphi)|\le\frac{11\kappa_e}{\nu_e}\,\delta.$$
--
--   Lemma 3 propagates the comparison between the flow over time and the hypothetical flow across one arc; it is the induction step of Theorem 1 on the fluid side.
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
--   - encoding: φ ∈ M_j with φ ∈ βℕ (and ϕ ∈ M_{j′} ∩ βℕ) → φ = iβ, ϕ = i′β with 1 ≤ i ≤ |N_j|, 1 ≤ i′ ≤ |N_{j′}|; reason: iβ ≤ m_j iff i ≤ ⌊m_j/β⌋; ℕ = {1, 2, …} as in the paper
--   - encoding: the context of the lemma (proof of Theorem 1, p.20): β/α < 1 and ν̂_e ≥ 2 → hypotheses `β/α < 1`, `∀ e′, 2 ≤ ν̂_{e′}`; reason: the paper's own conditions for Lemma 3
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, Lemma 3, p.14 (proof pp.14–16)

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_FlowOverTime
import Definitions.Def_PacketFlowConv_IsHypothetical

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, Lemma 3, p.14: "Consider an arc `e = uv`, a commodity `j ∈ J_e` and a particle
`φ ∈ M_j` with `φ ∈ βℕ`. Suppose there exists a `δ > α` with `|ℓ_{j′,u}(ϕ) − k_{j′,u}(ϕ)| ≤ δ` for all
commodities `j′ ∈ J_e`, and all particles `ϕ ∈ M_{j′}` with `ϕ ∈ βℕ` and `ℓ_{j′,u}(ϕ) ≤ ℓ_{j,u}(φ)` or
`k_{j′,u}(ϕ) ≤ k_{j,u}(φ)`. Then it holds that `|ℓ_{j,v}(φ) − k_{j,v}(φ)| ≤ 11κ_e/ν_e · δ`."

**Formalization Note.** "`φ ∈ M_j` with `φ ∈ βℕ`" is `φ = iβ` with `1 ≤ i ≤ |N_j|`; the same for
the particles `ϕ = i′β` of the hypothesis. The context is that of the proof of Theorem 1: a
feasible flow over time `f`, the packet routing at `(α, β)` with `β/α < 1` and `ν̂_e ≥ 2` for all
arcs ("The last two conditions are needed for Lemma 3", p.20), and a hypothetical flow on `e`. -/
theorem lemma_3 {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (f : FlowOverTime E J) (hf : I.IsFeasible f)
    (D : Discretization V E J) (hD : D.Valid) (hβα : D.β / D.α < 1)
    (hnu : ∀ e', 2 ≤ I.nuHat D e')
    (e : E) (hout : J → ℝ → ℝ) (hH : I.IsHypothetical D e hout)
    (j : J) (he : e ∈ I.P j) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ I.nPk D j)
    (δ : ℝ) (hδ : D.α < δ)
    (hclose : ∀ j' ∈ I.Je e, ∀ i' : ℕ, 1 ≤ i' → i' ≤ I.nPk D j' →
      (I.ell f j' (I.G.tail e) ((i' : ℝ) * D.β) ≤ I.ell f j (I.G.tail e) ((i : ℝ) * D.β) ∨
        I.kU D j' e ((i' : ℝ) * D.β) ≤ I.kU D j e ((i : ℝ) * D.β)) →
      |I.ell f j' (I.G.tail e) ((i' : ℝ) * D.β) - I.kU D j' e ((i' : ℝ) * D.β)| ≤ δ) :
    |I.ell f j (I.G.head e) ((i : ℝ) * D.β) - kV hout j ((i : ℝ) * D.β)| ≤
      11 * I.kappa e / I.ν e * δ := by sorry

end PacketFlowConv
