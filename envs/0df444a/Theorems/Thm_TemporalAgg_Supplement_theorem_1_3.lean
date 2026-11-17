-- Prove2me | Theorems.Thm_TemporalAgg_Supplement_theorem_1_3
-- name    : TemporalAgg.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:19:07.67756+00:00
-- url     : https://prove2.me/theorems/18965a81-3cf8-439f-83eb-7ce8096e7314
-- title:
--   Theorem 1.3 — temporal selection gives expected congestion $n^{\Omega(1)}$
-- statement:
--   Consider the adaptive temporal-selection process on random walks: an adaptive adversary produces graphs $G_1\supseteq G_2\supseteq\cdots\supseteq G_T$ on $n$ vertices by edge deletions and samples, for each vertex $v$, at most one random walk of length $\ell$ from $v$ in $G_{t(v)}$, at an adaptively chosen time $t(v)$.
--
--   There are absolute constants $C,c>0$ and $n_0$ such that for every $n\ge n_0$ there exist such a strategy with walk length $\ell\le C\ln n$ and horizon $1\le T\le C n$, and an edge $e$ that lies in $E(G_T)$ on every history, with
--
--   $$
--   \mathbb E\big[\text{congestion of } e \text{ at time } T\big]\ \ge\ n^{c}.
--   $$
--
--   The congestion counts the traversals of $e$, with multiplicity, by all walks sampled at times $\le T$. In the static setting, where all walks are sampled simultaneously, every edge has expected congestion $O(\log n)$; the theorem shows that sampling every walk once, but at adversarially chosen times in a shrinking graph, already defeats this by a polynomial factor (the temporal selection attack).
--
--   **Formalization Note** The process law is realized on the finite space of independent uniform random numbers $\xi_{v,i}\in\{0,\dots,n!-1\}$ that drive the walks; see the definition of the process.
--
--   Differences from the source:
--   - reading: T = O(n), length O(log n), expected congestion n^{Ω(1)} → ∃ C, c > 0 and n₀ such that for every n ≥ n₀: 1 ≤ T ≤ C·n, ℓ ≤ C·ln n, E[congestion] ≥ n^c; reason: asymptotic notation in an existence statement means absolute constants uniform in n, for all sufficiently large n (Preliminaries, p.14)
--   - encoding: adaptive strategy seeing the whole history; walks with fresh randomness → deterministic strategy reading the list of observed walks; walk of v driven by independent uniform numbers in {0,…,n!−1} (selState); reason: for a deterministic strategy the observed walks determine the history; the driven walk has the law of a random walk in the current graph
--   - encoding: e ∈ E(G_T) → e is an edge of G_T on every history; reason: the graphs, hence E(G_T), are random under an adaptive strategy; "some edge e ∈ E(G_T)" is one fixed edge never deleted by time T
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.3, p.6, Theorem 1.3 (restated and proved in App. A, pp.35–36)

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_TemporalAgg_Supplement_selState

namespace TemporalAgg.Supplement

/-- **Theorem 1.3** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against
Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.6;
restated and proved in App. A, pp.35–36).

There exists an adaptive adversarial strategy that produces a sequence of `T = O(n)` graphs
`G₁ ⊇ G₂ ⊇ ⋯ ⊇ G_T` on `n` vertices and samples, for each vertex `v`, at most one random walk of
length `O(log n)` from `v` in `G_{t(v)}` at an adaptively chosen time `t(v)`, such that some edge
`e ∈ E(G_T)` has expected congestion `n^{Ω(1)}` at time `T`.

**Formalization Note** The asymptotic notation is read with absolute constants `C, c > 0` and a
threshold `n₀`, uniform in `n`: for every `n ≥ n₀` there are a strategy (initial graph `G₁` on
`Fin n`, adaptive sampling and deletion rules) `σ`, a walk length `ℓ ≤ C·ln n`, a horizon
`1 ≤ T ≤ C·n` and an edge `e` of `G_T` (on every history) whose expected congestion at time `T`
is at least `n^c`. The process law is realized on the finite space
`Fin n → Fin ℓ → Fin n!` with the uniform distribution (see `selState`); `G_T` is
`(selState σ ℓ ξ (T − 1)).graph`. Each vertex is sampled at most once and graphs only shrink, by
construction of the process. -/
theorem theorem_1_3 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (σ : SelStrategy n) (ℓ T : ℕ) (e : Sym2 (Fin n)),
        1 ≤ T ∧ (T : ℝ) ≤ C * n ∧ (ℓ : ℝ) ≤ C * Real.log n ∧
        (∀ ξ : Fin n → Fin ℓ → Fin (Nat.factorial n),
          e ∈ (selState σ ℓ (fun v i => (ξ v i : ℕ)) (T - 1)).graph.edgeSet) ∧
        (n : ℝ) ^ c ≤ NoSignalPA.uniformExp (fun ξ : Fin n → Fin ℓ → Fin (Nat.factorial n) =>
          (selCongestion σ ℓ (fun v i => (ξ v i : ℕ)) T e : ℝ)) := by sorry

end TemporalAgg.Supplement
