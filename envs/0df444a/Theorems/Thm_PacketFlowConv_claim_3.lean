-- Prove2me | Theorems.Thm_PacketFlowConv_claim_3
-- name    : PacketFlowConv.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:22.292978+00:00
-- url     : https://prove2.me/theorems/edc170d0-dbe6-45ac-8ce6-ce7caf4ab76d
-- title:
--   Claim 3, p.16 — single-commodity view of one arc: $|k_v(\varphi)-\ell^D_v(\lceil\varphi/\beta\rceil)|\le\tilde C_1\sqrt\alpha+\varphi\tilde C_2\sqrt\alpha$
-- statement:
--   There are positive constants $\tilde C_1,\tilde C_2$, depending only on $\kappa_e$ and $\nu_e$, with the following property. For every valid instance and arc $e=uv$ there is $\alpha_0>0$ such that for every valid discretization with $\alpha<\alpha_0$, $\beta/\alpha<1$, $\hat\nu_{e'}\ge2$ for all arcs and $\bar u_j\alpha/\beta\ge2$ for all commodities, every hypothetical flow on $e$, and every particle $\varphi\ge0$ of the aggregated flow on $e$ whose packet $i=\lceil\varphi/\beta\rceil$ satisfies $1\le i\le\sum_{j\in J_e}|N_j|$,
--   $$\big|k_v(\varphi)-\ell^D_v(i)\big|\le\tilde C_1\sqrt\alpha+\varphi\,\tilde C_2\sqrt\alpha,$$
--   where $k_v(\varphi)=\min\{\theta\ge0:H^-_e(\theta)=\varphi\}$ and $\ell^D_v(i)=\min\{\theta\ge0:G^-_e(\theta)=i\beta\}$.
--
--   On one arc both models are FIFO, so the paper treats all particles as one commodity; the claim compares the hypothetical fluid exit times with the refined packet exit times.
--
--   Differences from the source:
--   - generalization: a directed graph G = (V, E) → a finite directed multigraph (published `Network V E` with `tail`, `head`; parallel arcs allowed); reason: every directed graph is such a multigraph, so the statement specializes to the source's
--   - generalization: ties in Algorithm 1 are broken "arbitrarily (but deterministically)"; released packets are ordered "by packet index" → every tie-break rule `tb v e t n S ∈ S` (depending on node, arc, step, round and tied set) and every release order `σ` increasing in the index within each commodity; reason: the paper fixes one unspecified deterministic rule, and its index order leaves the order across commodities open; each such choice is one instance of the Lean family
--   - encoding: B_e(t) and L⁻_e(t) are "suffixes" of Q_e(t) → the longest initial segment (oldest packets) of the queue with entrance step ≤ t − τ̂_e, and its first ⌊ν̂_e(t)⌋ packets; reason: Algorithm 2 appends entering packets at the end and p.4 says "the first ⌊ν̂_e(t)⌋ packets in line": the head of the queue is meant
--   - encoding: u_j, g^±_{j,e} defined on ℝ≥0 → functions on ℝ vanishing before 0; reason: Lean convention; the values on [0, ∞) and all integrals from 0 are unchanged
--   - encoding: a simple o_j-d_j path P_j → a simple o_j-d_j path P_j that is nonempty (`Valid.path_ne`, i.e. o_j ≠ d_j); reason: for o_j = d_j the empty path leaves ℓ^D_{j,v} undefined (it needs an arc uv or vw ∈ P_j, p.10), and no feasible flow over time exists (conservation (2) at o_j = d_j forces u_j = 0 a.e., contradicting m_j > 0); only these cases are excluded
--   - encoding: "α sufficiently small", "β/α sufficiently small" (standing assumptions of §5, p.12, made explicit after Theorem 1) → hypotheses β/α < 1, ν_e α/β ≥ 2 for all arcs, ū_j α/β ≥ 2 for all j, and α below a threshold α₀ (existential); reason: the paper's own conditions
--   - encoding: (3): f⁻_e = ν_e if z_e > 0, min{f⁺_e(θ − τ_e), ν_e} if z_e = 0 → `if 0 < z_e θ then ν_e else min (f⁺_e (θ − τ_e)) ν_e`; reason: queues are volumes; the if-then-else keeps them nonnegative and excludes no flow of the source
--   - encoding: (4) with ϑ = min { ξ ≤ θ | T_e(ξ) = θ } → (4) required for every least element ϑ of that set (`IsLeast`); reason: the minimum always exists for rates vanishing before 0, so nothing is dropped
--   - reading: constants C̃1, C̃2 "that only depend on the instance properties" → functions C̃₁(κ_e, ν_e), C̃₂(κ_e, ν_e) chosen before the instance; reason: the paper's δ(φ) (p.19) depends only on ν_e and κ_e; this is the stronger of the two readings
--   - reading: packets i ∈ N = {1, …, Σ_{j∈J} |N_j|} → 1 ≤ i ≤ Σ_{j∈J_e} |N_j|; reason: on the single arc e only the commodities of J_e flow; for larger i the minima defining k_v and ℓ^D_v are over empty sets
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, Claim 3 (in the proof of Lemma 4), p.16 (δ(φ) on p.19)

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization
import Definitions.Def_PacketFlowConv_IsHypothetical

open MeasureTheory

namespace PacketFlowConv

/-- Sering, Vargas Koch, Ziemke, *Convergence of a Packet Routing Model to Flows Over Time*, arXiv:2105.13202v2, Claim 3 (proof of Lemma 4), p.16, in the aggregated single-commodity view of one
arc `e = uv` (p.16): "There exists constants `C̃1` and `C̃2` that only depend on the instance properties
such that for all `φ ∈ M` with `i = ⌈φ/β⌉ ∈ N` it holds that `|k_v(φ) − ℓ^D_v(i)| ≤ δ(φ)` with
`δ(φ) ≤ C̃1 · √α + φ · C̃2 · √α`." Here `k_v(φ) = min { θ ≥ 0 | H⁻_e(θ) = φ }` and
`ℓ^D_v(i) = min { θ ≥ 0 | G⁻_e(θ) = iβ }`.

**Formalization Note.** `C̃1, C̃2` are functions of `(κ_e, ν_e)` (the paper's `δ`, p.19, depends only
on `ν_e`, `κ_e`), chosen before the instance; the claim sits in Lemma 4 ("for sufficiently small
`α`"), so it is asserted for `α` below an instance-dependent threshold, under the standing
assumptions of §5 (`β/α < 1`, `ν̂_e ≥ 2` for all arcs, `ū_j α/β ≥ 2` for all commodities, p.12).
`N` is read as the packets on `e`, `{1, …, Σ_{j ∈ J_e} |N_j|}` (the range of `G⁺_e`). -/
theorem claim_3 :
    ∃ C₁ C₂ : ℝ → ℝ → ℝ, (∀ a b, 0 < C₁ a b ∧ 0 < C₂ a b) ∧
    ∀ {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      [Fintype J] [DecidableEq J]
      (I : Instance V E J), I.Valid → ∀ e : E, ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ D : Discretization V E J, D.Valid → D.α < α₀ → D.β / D.α < 1 → (∀ e', 2 ≤ I.nuHat D e') →
        (∀ j', 2 ≤ I.supRate j' * D.α / D.β) →
      ∀ hout : J → ℝ → ℝ, I.IsHypothetical D e hout →
      ∀ φ : ℝ, 0 ≤ φ → 1 ≤ ⌈φ / D.β⌉₊ → ⌈φ / D.β⌉₊ ≤ ∑ j ∈ I.Je e, I.nPk D j →
      |kVagg hout φ - I.ellDVagg D e ⌈φ / D.β⌉₊| ≤
        C₁ (I.kappa e) (I.ν e) * Real.sqrt D.α + φ * C₂ (I.kappa e) (I.ν e) * Real.sqrt D.α := by sorry

end PacketFlowConv
