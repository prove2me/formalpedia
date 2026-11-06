-- Prove2me | Theorems.Thm_TemporalVoter_corollary_3_6
-- name    : TemporalVoter.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:03.746487+00:00
-- url     : https://prove2.me/theorems/835c54f7-1f2d-4f25-95d1-3c8df837bbac
-- title:
--   Corollary 3.6 — drift of $\psi$ over $[T_j,T_{j+1})$ in terms of the accumulated cut $\mu$
-- statement:
--   Consider the standard two-opinion voter model on a temporal graph with fixed degrees and minimum degree $d_{\min}$, from any initial state, with interval lengths $\Delta_j\ge1$ and the stopping times $T_j$ of Definition 3.2. Let $j,t_j\ge0$, let $H$ be a possible value of $\mathcal H_{T_j}$ with $T_j=t_j$, and let $s$ be the value of $S_{T_j}$ it determines. Let
--   $$\mu:=\mathbb E\Bigl[\sum_{t=t_j}^{T_{j+1}-1}e_t(S_t,\overline{S_t})\ \Big|\ \mathcal H_{T_j}=H\Bigr].$$
--   Then
--   $$\mathbb E\bigl[\psi(S_{T_{j+1}})-\psi(s)\bigm|\mathcal H_{T_j}=H\bigr]\ \le\ -\frac{d_{\min}}{24\sqrt6\,\psi(s)^3}\,\mu.$$
--
--   It sums the one-step drift of Lemma 3.5 over an interval on which the minority volume stays within a factor $3/2$ of its starting value.
--
--   **Formalization Note** For $s=\emptyset$ the right-hand side is $0$ (Lean's division by zero), and then $T_{j+1}=t_j$ so the left-hand side is $0$ too, as in the paper's proof.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: a possible value H of H_{T_j}, and E[· | H_{T_j} = H] → a path h and t_j with 0 < ℙ(T_j = t_j, ξ_s = h s for s ≤ t_j); elementary conditioning μ[|E] on that event; reason: histories are finite sequences of subsets, so a possible value is one of positive probability (paper.md R7)
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
--   - generalization: the setting of §3 up to the end of §3.3 (p.15: "let the following be defined as in the statement of Theorem 3.1"): integers Δ_j ≥ 1, φ_j ∈ [0, 1] with φ^{I_j}(G) ≥ φ_j, J < ∞, and a fixed initial minority set S_0 → only Δ_j ≥ 1 is assumed; any initial state σ₀; reason: the statement involves no φ and no J, and the proof does not use them; every instance of the setting of §3 is an instance of the Lean statement
--   - encoding: for s = ∅ the right side is −d_min µ/(24√6 ψ(s)³) with ψ(s) = 0 and µ = 0, undefined on the page (the proof calls this case immediate) → no hypothesis s ≠ ∅; Lean's x / 0 = 0 makes the right side 0, and the left side is 0 because T_{j+1} = t_j; reason: the page has no value there to differ from; the instances with s ≠ ∅ are unchanged
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Corollary 3.6, p.16

import Mathlib
import Definitions.Def_TemporalVoter_minoritySet

open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- **Corollary 3.6** (arXiv:2606.13374, version of 2 Nov 2026, p.16): in the two-opinion voter
model with interval lengths `Δ_0, Δ_1, … ≥ 1` and stopping times `T_j` (Definition 3.2), let
`j, t_j ≥ 0`, let `H` be a possible value of `H_{T_j}` (with `T_j = t_j`) and `s` the value of
`S_{T_j}` it determines. With `µ := E[∑_{t=t_j}^{T_{j+1}−1} e_t(S_t, S̄_t) | H_{T_j} = H]`,
`E[ψ(S_{T_{j+1}}) − ψ(s) | H_{T_j} = H] ≤ −d_min µ/(24√6 ψ(s)³)`.

**Formalization Note** For `s = ∅` the right side is `−d_min·µ/0`, which Lean evaluates to `0`;
there `T_{j+1} = t_j` and both sides are `0`, as in the paper's proof. -/
theorem corollary_3_6 {V : Type} [Fintype V] (T : TemporalGraph V) (σ₀ : V → Fin 2)
    (Δ : ℕ → ℕ) (hΔ : ∀ j, 1 ≤ Δ j) (j tj : ℕ) (h : ℕ → V → Fin 2)
    (hpos : 0 < voterLaw T 2 σ₀ (stoppedHistoryEvent T Δ j tj h)) :
    ∫ ω, (psi T (minoritySet T (ω (stoppingTimes T Δ (j + 1) ω))) - psi T (minoritySet T (h tj)))
        ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h] ≤
      -(T.dmin / (24 * Real.sqrt 6 * psi T (minoritySet T (h tj)) ^ 3)) *
        ∫ ω, (∑ t ∈ Finset.Ico tj (stoppingTimes T Δ (j + 1) ω), T.cut t (minoritySet T (ω t)))
          ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h] := by sorry

end TemporalVoter
