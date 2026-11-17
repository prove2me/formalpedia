-- Prove2me | Theorems.Thm_TemporalAgg_Supplement_theorem_1_4
-- name    : TemporalAgg.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:19:44.306216+00:00
-- url     : https://prove2.me/theorems/386a011c-4124-49db-84db-38758621672c
-- title:
--   Theorem 1.4 — temporal selection defeats proactive resampling
-- statement:
--   Consider random walks maintained by proactive resampling against an adaptive adversary that only deletes edges: whenever an edge is deleted, every walk traversing it is resampled (an adversarial sample), and every walk with an adversarial sample at time $s$ is also resampled at times $s+2^i$, $i\ge0$; all samples are random walks in the current graph.
--
--   There are absolute constants $C,c>0$ and $n_0$ such that for every $n\ge n_0$ there exist a graph $G$ on $n$ vertices, a set of sources (each vertex the source of at most one walk) with common length $\ell\le C\ln n$, and an adaptive edge-deleting strategy that keeps every source of degree at least $1$ at all times, together with a time $t\le Cn$ and an edge $e$ of $G$ such that
--
--   $$
--   \mathbb E\big[\text{congestion of } e \text{ at time } t\big]\ \ge\ n^{c}.
--   $$
--
--   Proactive resampling was designed against adversaries that resample one object until it is bad; this theorem shows that it does not protect against adversaries that change the distributions between samples. It contrasts with Greedy Temporal Aggregation, which keeps the congestion polylogarithmic.
--
--   **Formalization Note** The expectation is over independent uniform random numbers $\xi_{v,s,i}\in\{0,\dots,n!-1\}$, $s\le t$, that drive the samples; see the definition of the process.
--
--   Differences from the source:
--   - reading: length O(log n), within O(n) time steps, expected congestion n^{Ω(1)} → ∃ C, c > 0 and n₀ such that for every n ≥ n₀: ℓ ≤ C·ln n and some time t ≤ C·n and edge e have E[congestion] ≥ n^c; reason: asymptotic notation in an existence statement means absolute constants uniform in n, for all sufficiently large n (Preliminaries, p.14)
--   - reading: adaptive adversarial strategy that only deletes edges (in the walk setting of §1.2, k_v ≤ deg(v)) → the strategy keeps every source of degree ≥ 1 at all times on every history; reason: the setting of §1.2 requires k_v ≤ deg_{G_t}(v); with one walk per source this is degree ≥ 1, which the proof states it maintains (p.37)
--   - encoding: walks maintained by proactive resampling, fresh random walks → prwState: deterministic strategy reading the walk-configuration history; samples driven by independent uniform numbers in {0,…,n!−1}; reason: for a deterministic strategy this history is the whole history; the driven walks have the law of random walks in the current graph
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.3, p.6, Theorem 1.4 (restated and proved in App. A, pp.36–37)

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_TemporalAgg_Supplement_prwState

namespace TemporalAgg.Supplement

/-- **Theorem 1.4** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against
Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.6;
restated and proved in App. A, pp.36–37).

There exists a graph `G` on `n` vertices, where each vertex is the source of at most one random
walk of length `O(log n)`, and an adaptive adversarial strategy that only deletes edges, such that,
if the walks are maintained by proactive resampling, then within `O(n)` time steps some edge has
expected congestion `n^{Ω(1)}`.

**Formalization Note** The asymptotic notation is read with absolute constants `C, c > 0` and a
threshold `n₀`, uniform in `n`: for every `n ≥ n₀` there are a graph `G` on `Fin n`, a set `src`
of sources (one walk each), a length `ℓ ≤ C·ln n`, and an edge-deleting strategy `σ` that keeps
every source of degree `≥ 1` at all times on every history (the setting of §1.2 requires
`k_v ≤ deg(v)`), together with a time `t ≤ C·n` and an edge `e` of `G` whose expected congestion
at the end of step `t` is at least `n^c`. The walks are maintained by proactive resampling exactly
as in `prwState` (deletions; forced resamples of walks through deleted edges, adversarial, each
starting its schedule `s + 2ⁱ`; proactive resamples; all in the current graph). The expectation is
over the first `t + 1` steps' randomness, uniform on `Fin n → Fin (t+1) → Fin ℓ → Fin n!`. -/
theorem theorem_1_4 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (G : SimpleGraph (Fin n)) (src : Finset (Fin n)) (ℓ : ℕ) (σ : DeletionStrategy n),
        (ℓ : ℝ) ≤ C * Real.log n ∧
        (∀ (ξ : Fin n → ℕ → Fin ℓ → ℕ) (t : ℕ), ∀ v ∈ src,
          ∃ w, (prwState G src ℓ σ ξ t).graph.Adj v w) ∧
        ∃ t : ℕ, (t : ℝ) ≤ C * n ∧ ∃ e ∈ G.edgeSet,
          (n : ℝ) ^ c ≤ NoSignalPA.uniformExp (fun η : Fin n → Fin (t + 1) → Fin ℓ → Fin (Nat.factorial n) =>
            (prwCongestion G src ℓ σ (prwRand η) t e : ℝ)) := by sorry

end TemporalAgg.Supplement
