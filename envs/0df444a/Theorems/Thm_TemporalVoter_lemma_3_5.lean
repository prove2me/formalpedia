-- Prove2me | Theorems.Thm_TemporalVoter_lemma_3_5
-- name    : TemporalVoter.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:48.973178+00:00
-- url     : https://prove2.me/theorems/92b67898-879b-478a-a17d-322e58f65734
-- title:
--   Lemma 3.5 — one-step backward drift of $\psi(S_t)=\sqrt{\mathrm{Vol}(S_t)}$
-- statement:
--   In the standard two-opinion voter model on a temporal graph with fixed degrees and minimum degree $d_{\min}$, from any initial state, let $t\ge0$, let $H$ be a possible value of the history $\mathcal H_t$ and let $s_t$ be the value of $S_t$ it determines. If $s_t\ne\emptyset$, then
--   $$\mathbb E\bigl[\psi(S_{t+1})\bigm|\mathcal H_t=H\bigr]\ \le\ \psi(s_t)-\frac{d_{\min}}{32}\cdot\frac{e_t(s_t,\overline{s_t})}{\psi(s_t)^3},\qquad \psi(S)=\sqrt{\mathrm{Vol}(S)}.$$
--
--   The square root of the minority volume drifts down at every step, at a rate set by the current cut; this is the per-step input to the stable-interval analysis.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - encoding: a possible value H_t of H_t, and E[· | H_t = H_t] → a path h with 0 < ℙ(ξ_s = h s for s ≤ t); elementary conditioning on that event; reason: paper.md R7
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
--   - generalization: the setting of §3 up to the end of §3.3 (p.15: "let the following be defined as in the statement of Theorem 3.1"): integers Δ_j ≥ 1, φ_j ∈ [0, 1] with φ^{I_j}(G) ≥ φ_j, J < ∞, and a fixed initial minority set S_0 → none of these is assumed; any initial state σ₀; reason: the lemma is about the non-embedded model and neither its statement nor its proof involves Δ, φ or J; every instance of the setting of §3 is an instance of the Lean statement
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Lemma 3.5, p.16

import Mathlib
import Definitions.Def_TemporalVoter_minoritySet

open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- **Lemma 3.5** (arXiv:2606.13374, version of 2 Nov 2026, p.16): in the two-opinion voter model,
let `t ≥ 0`, let `H` be a possible value of `H_t` and `s_t ≠ ∅` the value of `S_t` it determines.
Then `E[ψ(S_{t+1}) | H_t = H] ≤ ψ(s_t) − (d_min/32) · e_t(s_t, s̄_t)/ψ(s_t)³`, `ψ(S) = √Vol(S)`.

**Formalization Note** "Possible value" is `0 < ℙ(H_t = H)` and the conditional expectation is
elementary conditioning on `{H_t = H}`. -/
theorem lemma_3_5 {V : Type} [Fintype V] (T : TemporalGraph V) (σ₀ : V → Fin 2) (t : ℕ)
    (h : ℕ → V → Fin 2) (hpos : 0 < voterLaw T 2 σ₀ (historyEvent t h))
    (hs : minoritySet T (h t) ≠ ∅) :
    ∫ ω, psi T (minoritySet T (ω (t + 1))) ∂(voterLaw T 2 σ₀)[|historyEvent t h] ≤
      psi T (minoritySet T (h t)) -
        T.dmin / 32 * (T.cut t (minoritySet T (h t)) / psi T (minoritySet T (h t)) ^ 3) := by sorry

end TemporalVoter
