-- Prove2me | Theorems.Thm_TemporalVoter_lemma_3_8
-- name    : TemporalVoter.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:16.162241+00:00
-- url     : https://prove2.me/theorems/a6bcc308-c994-44aa-99aa-e8738b2859b6
-- title:
--   Lemma 3.8 — drift of $\psi$ over $[T_j,T_{j+1})$: nonpositive, and $\le -d_{\min}\phi_j/(500\psi)$ when stable
-- statement:
--   Assume the hypotheses of Theorem 3.1 (fixed degrees; $\Delta_j\ge1$; $\phi_j\in[0,1]$; $\phi^{I_j}(\mathcal G)\ge\phi_j$ for all $j$) and run the standard two-opinion voter model from any initial state, with the stopping times $T_j$. Let $j,t_j\ge0$, let $H$ be a possible value of $\mathcal H_{T_j}$ with $T_j=t_j$, and let $s$ be the value of $S_{T_j}$ it determines. Then
--   $$\mathbb E\bigl[\psi(S_{T_{j+1}})-\psi(s)\bigm|\mathcal H_{T_j}=H\bigr]\le0.$$
--   If in addition $s\ne\emptyset$ and $H$ is stable, then
--   $$\mathbb E\bigl[\psi(S_{T_{j+1}})-\psi(s)\bigm|\mathcal H_{T_j}=H\bigr]\le-\frac{d_{\min}\,\phi_j}{500\,\psi(s)}.$$
--
--   This is the main estimate for stable intervals.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: a possible value H of H_{T_j}, and E[· | H_{T_j} = H] → a path h and t_j with 0 < ℙ(T_j = t_j, ξ_s = h s for s ≤ t_j); elementary conditioning μ[|E] on that event; reason: histories are finite sequences of subsets, so a possible value is one of positive probability (paper.md R7)
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
--   - generalization: the setting of §3 up to the end of §3.3 (p.15: "let the following be defined as in the statement of Theorem 3.1"): integers Δ_j ≥ 1, φ_j ∈ [0, 1] with φ^{I_j}(G) ≥ φ_j, J < ∞, and a fixed initial minority set S_0 → Δ_j ≥ 1, φ_j ∈ [0, 1] and φ^{I_j}(G) ≥ φ_j are assumed, J < ∞ is not; any initial state σ₀; reason: the statement and the proof do not involve J; every instance of the setting of §3 is an instance of the Lean statement
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Lemma 3.8, p.20

import Mathlib
import Definitions.Def_TemporalVoter_minoritySet

open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- **Lemma 3.8** (arXiv:2606.13374, version of 2 Nov 2026, p.20), under the standing hypotheses of
Theorem 3.1: let `j, t_j ≥ 0`, let `H` be a possible value of `H_{T_j}` (with `T_j = t_j`) and `s`
the value of `S_{T_j}` it determines. Then `E[ψ(S_{T_{j+1}}) − ψ(s) | H_{T_j} = H] ≤ 0`; if in
addition `s ≠ ∅` and `H` is stable, then
`E[ψ(S_{T_{j+1}}) − ψ(s) | H_{T_j} = H] ≤ −d_min φ_j/(500 ψ(s))`. -/
theorem lemma_3_8 {V : Type} [Fintype V] (T : TemporalGraph V) (σ₀ : V → Fin 2)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (hΔ : ∀ j, 1 ≤ Δ j) (hφ : ∀ j, 0 ≤ φ j ∧ φ j ≤ 1)
    (hcond : ∀ j, φ j ≤ intervalCond T (Iminus Δ j) (Iplus Δ j))
    (j tj : ℕ) (h : ℕ → V → Fin 2)
    (hpos : 0 < voterLaw T 2 σ₀ (stoppedHistoryEvent T Δ j tj h)) :
    ∫ ω, (psi T (minoritySet T (ω (stoppingTimes T Δ (j + 1) ω))) - psi T (minoritySet T (h tj)))
        ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h] ≤ 0 ∧
      (minoritySet T (h tj) ≠ ∅ → IsStable T σ₀ Δ j tj h →
        ∫ ω, (psi T (minoritySet T (ω (stoppingTimes T Δ (j + 1) ω))) -
            psi T (minoritySet T (h tj))) ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h] ≤
          -(T.dmin * φ j / (500 * psi T (minoritySet T (h tj))))) := by sorry

end TemporalVoter
