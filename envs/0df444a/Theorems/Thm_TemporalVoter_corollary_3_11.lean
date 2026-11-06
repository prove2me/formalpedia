-- Prove2me | Theorems.Thm_TemporalVoter_corollary_3_11
-- name    : TemporalVoter.corollary_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:04.385867+00:00
-- url     : https://prove2.me/theorems/97d51e26-ca82-42b6-b78f-d763f11be371
-- title:
--   Corollary 3.11 — drift of $\chi=\log(1+\mathrm{Vol})$: nonpositive, and $\le-10^{-4}$ when unstable
-- statement:
--   In the standard two-opinion voter model on a temporal graph with fixed degrees, from any initial state, with interval lengths $\Delta_j\ge1$ and stopping times $T_j$, let $j,t_j\ge0$, let $H$ be a possible value of $\mathcal H_{T_j}$ with $T_j=t_j$, and let $s$ be the value of $S_{T_j}$ it determines. With $\chi(S)=\log(1+\mathrm{Vol}(S))$,
--   $$\mathbb E\bigl[\chi(S_{T_{j+1}})-\chi(s)\bigm|\mathcal H_{T_j}=H\bigr]\le0.$$
--   If in addition $s\ne\emptyset$ and $H$ is unstable, then
--   $$\mathbb E\bigl[\chi(S_{T_{j+1}})-\chi(s)\bigm|\mathcal H_{T_j}=H\bigr]\le-10^{-4}.$$
--
--   This is the estimate for unstable intervals; together with Lemma 3.8 it gives the drift of the potential used to prove Theorem 3.1.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: a possible value H of H_{T_j}, and E[· | H_{T_j} = H] → a path h and t_j with 0 < ℙ(T_j = t_j, ξ_s = h s for s ≤ t_j); elementary conditioning μ[|E] on that event; reason: histories are finite sequences of subsets, so a possible value is one of positive probability (paper.md R7)
--   - reading: second display: χ(Vol(S_{T_{j+1}})) − χ(Vol(s_{t_j})) → chi T (S_{T_{j+1}}) − chi T s, i.e. log(1 + Vol(·)) of the sets; reason: χ is defined on sets (Definition 3.10) and the first display writes χ(S); this is the only meaning that typechecks (paper.md R8)
--   - encoding: 10⁻⁴ → 1/10000; reason: same number
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
--   - generalization: the setting of §3 up to the end of §3.3 (p.15: "let the following be defined as in the statement of Theorem 3.1"): integers Δ_j ≥ 1, φ_j ∈ [0, 1] with φ^{I_j}(G) ≥ φ_j, J < ∞, and a fixed initial minority set S_0 → only Δ_j ≥ 1 is assumed; any initial state σ₀; reason: the statement involves no φ and no J, and the proof does not use them; every instance of the setting of §3 is an instance of the Lean statement
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Corollary 3.11, p.21

import Mathlib
import Definitions.Def_TemporalVoter_minoritySet

open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- **Corollary 3.11** (arXiv:2606.13374, version of 2 Nov 2026, p.21): in the two-opinion voter
model with interval lengths `Δ_j ≥ 1`, let `j, t_j ≥ 0`, let `H` be a possible value of `H_{T_j}`
(with `T_j = t_j`) and `s` the value of `S_{T_j}` it determines. Then
`E[χ(S_{T_{j+1}}) − χ(s) | H_{T_j} = H] ≤ 0`; if in addition `s ≠ ∅` and `H` is unstable, then
`E[χ(S_{T_{j+1}}) − χ(s) | H_{T_j} = H] ≤ −10⁻⁴`, where `χ(S) = log(1 + Vol(S))`.

**Formalization Note** The second display of the paper writes `χ(Vol(·))`; `χ` is defined on sets
(Definition 3.10), so it is read as `χ(·)`. -/
theorem corollary_3_11 {V : Type} [Fintype V] (T : TemporalGraph V) (σ₀ : V → Fin 2)
    (Δ : ℕ → ℕ) (hΔ : ∀ j, 1 ≤ Δ j) (j tj : ℕ) (h : ℕ → V → Fin 2)
    (hpos : 0 < voterLaw T 2 σ₀ (stoppedHistoryEvent T Δ j tj h)) :
    ∫ ω, (chi T (minoritySet T (ω (stoppingTimes T Δ (j + 1) ω))) - chi T (minoritySet T (h tj)))
        ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h] ≤ 0 ∧
      (minoritySet T (h tj) ≠ ∅ → ¬ IsStable T σ₀ Δ j tj h →
        ∫ ω, (chi T (minoritySet T (ω (stoppingTimes T Δ (j + 1) ω))) -
            chi T (minoritySet T (h tj))) ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h] ≤
          -(1 / 10000 : ℝ)) := by sorry

end TemporalVoter
