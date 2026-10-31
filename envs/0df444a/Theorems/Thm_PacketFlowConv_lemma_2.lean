-- Prove2me | Theorems.Thm_PacketFlowConv_lemma_2
-- name    : PacketFlowConv.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:49.808499+00:00
-- url     : https://prove2.me/theorems/922f018b-48a2-414b-ad05-860b906d4f41
-- title:
--   Lemma 2, p.12 (corrected: $\theta$ a refined entrance time of a $j$-packet) — $|q^D_{j,e}(\theta)-z^D_e(\theta+\lceil\tau_e\rceil_\alpha)/\nu_e|\le2\alpha+\alpha\kappa_e/\nu_e+\beta/\nu_e$
-- statement:
--   Let the instance and the discretization be valid with $\beta/\alpha<1$ (§5, p.12). Let $e=uv$ be an arc of $P_j$, $i\in N_j$, and $\theta=\ell^D_{j,u}(i)$ the refined time at which packet $i$ enters $e$. Then
--   $$\Big|q^D_{j,e}(\theta)-\frac{z^D_e(\theta+\lceil\tau_e\rceil_\alpha)}{\nu_e}\Big|\le2\alpha+\frac{\alpha\kappa_e}{\nu_e}+\frac{\beta}{\nu_e}.$$
--
--   The waiting time of the packet model is, up to $O(\alpha+\beta)$, the total queue divided by the capacity, as in the flow over time.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: packets i ∈ N_j = {1, …, ⌊m_j/β⌋}, time steps t ∈ ℕ₀, times αt → packets `(j, i) : J × ℕ` with `1 ≤ i ≤ ⌊m_j/β⌋₊`, steps `t : ℕ`; reason: the same objects; the guard on i excludes only non-packets
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
--   - correction: "for every θ ∈ ℝ≥0" → θ = ℓ^D_{j,u}(i) for a packet i ∈ N_j; reason: false as printed: one arc, τ = ν = 1, u₁ = 1 on [0,1], u₂ = 10 on [5,6], α = 1/100, β = 10⁻⁴, θ = 6 give q^D_{1,e}(6) = 0 but z^D_e(7)/ν_e ≥ 8.9 > 0.15 ≈ 2α + ακ_e/ν_e + β/ν_e (κ_e = 13); the proof compares packets of j and j′ entering at the same refined time, so it needs a j-packet entering at θ
--   - encoding: the standing assumption "β/α is assumed to be smaller than 1" (p.12) → hypothesis `β/α < 1`; reason: the paper's own assumption, used through κ_e
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, Lemma 2, p.12 (proof pp.12–13)

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, Lemma 2, p.12, **corrected**: for an arc `e = uv`, a commodity `j ∈ J_e` and
`θ = ℓ^D_{j,u}(i)` the refined entrance time of a packet `i ∈ N_j` into `e`, under `β/α < 1`
(§5, p.12),
`|q^D_{j,e}(θ) − z^D_e(θ + ⌈τ_e⌉_α)/ν_e| ≤ 2α + ακ_e/ν_e + β/ν_e`.

**Formalization Note.** The printed lemma claims the bound "for every `θ ∈ ℝ≥0`"; that is false
with two commodities (one arc, `τ = ν = 1`, `u₁ = 1` on `[0,1]`, `u₂ = 10` on `[5,6]`, `α = 1/100`,
`β = 10⁻⁴`, `θ = 6`: the left side is `≥ 8.9`, the right side `≈ 0.15`). The proof compares packets
of `j` and `j′` "entering at the same refined time", so it needs a packet of `j` entering at `θ`. -/
theorem lemma_2 {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (I : Instance V E J) (hI : I.Valid) (D : Discretization V E J) (hD : D.Valid)
    (hβα : D.β / D.α < 1) (j : J) (e : E) (he : e ∈ I.P j) (i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ I.nPk D j) :
    |I.qD D j e (I.ellD D j (I.G.tail e) i) -
        I.zDTot D e (I.ellD D j (I.G.tail e) i + ceilGrid D.α (I.τ e)) / I.ν e| ≤
      2 * D.α + D.α * I.kappa e / I.ν e + D.β / I.ν e := by sorry

end PacketFlowConv
