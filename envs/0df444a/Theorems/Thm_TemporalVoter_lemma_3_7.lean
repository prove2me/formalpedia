-- Prove2me | Theorems.Thm_TemporalVoter_lemma_3_7
-- name    : TemporalVoter.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:50.255843+00:00
-- url     : https://prove2.me/theorems/ee0b5a47-25cc-441c-80df-5a6ebb6a994d
-- title:
--   Lemma 3.7 — on a stable interval the accumulated cut is at least $\phi_j\mathrm{Vol}(s)/8$
-- statement:
--   Assume the hypotheses of Theorem 3.1: $\mathcal G$ is a temporal graph with fixed degrees, $\Delta_0,\Delta_1,\ldots\ge1$ are integers and $\phi_0,\phi_1,\ldots\in[0,1]$ satisfy $\phi^{I_j}(\mathcal G)\ge\phi_j$ for all $j$, where $I_j=[I^-_j,I^+_j]$. Run the standard two-opinion voter model from any initial state, with the stopping times $T_j$. Let $j,t_j\ge0$, let $H$ be a **stable** possible value of $\mathcal H_{T_j}$ with $T_j=t_j$, and let $s\ne\emptyset$ be the value of $S_{T_j}$ it determines. Then
--   $$\mu:=\mathbb E\Bigl[\sum_{t=t_j}^{T_{j+1}-1}e_t(S_t,\overline{S_t})\ \Big|\ \mathcal H_{T_j}=H\Bigr]\ \ge\ \frac{\phi_j\,\mathrm{Vol}(s)}{8}.$$
--
--   On a stable interval the one good step guaranteed by $\phi^{I_j}(\mathcal G)\ge\phi_j$ still produces a large cut in expectation, although the minority set may have moved.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: a possible value H of H_{T_j}, and E[· | H_{T_j} = H] → a path h and t_j with 0 < ℙ(T_j = t_j, ξ_s = h s for s ≤ t_j); elementary conditioning μ[|E] on that event; reason: histories are finite sequences of subsets, so a possible value is one of positive probability (paper.md R7)
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
--   - generalization: the setting of §3 up to the end of §3.3 (p.15: "let the following be defined as in the statement of Theorem 3.1"): integers Δ_j ≥ 1, φ_j ∈ [0, 1] with φ^{I_j}(G) ≥ φ_j, J < ∞, and a fixed initial minority set S_0 → Δ_j ≥ 1, φ_j ∈ [0, 1] and φ^{I_j}(G) ≥ φ_j are assumed, J < ∞ is not; any initial state σ₀; reason: the statement and the proof do not involve J; every instance of the setting of §3 is an instance of the Lean statement
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Lemma 3.7, p.18

import Mathlib
import Definitions.Def_TemporalVoter_minoritySet

open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- **Lemma 3.7** (arXiv:2606.13374, version of 2 Nov 2026, p.18), under the standing hypotheses of
Theorem 3.1 (`Δ_j ≥ 1`, `φ_j ∈ [0, 1]`, `φ^{I_j}(G) ≥ φ_j` for all `j`): let `j, t_j ≥ 0`, let `H`
be a stable possible value of `H_{T_j}` (with `T_j = t_j`) and `s ≠ ∅` the value of `S_{T_j}` it
determines. Then `µ := E[∑_{t=t_j}^{T_{j+1}−1} e_t(S_t, S̄_t) | H_{T_j} = H] ≥ φ_j Vol(s)/8`. -/
theorem lemma_3_7 {V : Type} [Fintype V] (T : TemporalGraph V) (σ₀ : V → Fin 2)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (hΔ : ∀ j, 1 ≤ Δ j) (hφ : ∀ j, 0 ≤ φ j ∧ φ j ≤ 1)
    (hcond : ∀ j, φ j ≤ intervalCond T (Iminus Δ j) (Iplus Δ j))
    (j tj : ℕ) (h : ℕ → V → Fin 2)
    (hpos : 0 < voterLaw T 2 σ₀ (stoppedHistoryEvent T Δ j tj h))
    (hstable : IsStable T σ₀ Δ j tj h) (hs : minoritySet T (h tj) ≠ ∅) :
    φ j * T.vol (minoritySet T (h tj)) / 8 ≤
      ∫ ω, (∑ t ∈ Finset.Ico tj (stoppingTimes T Δ (j + 1) ω), T.cut t (minoritySet T (ω t)))
        ∂(voterLaw T 2 σ₀)[|stoppedHistoryEvent T Δ j tj h] := by sorry

end TemporalVoter
