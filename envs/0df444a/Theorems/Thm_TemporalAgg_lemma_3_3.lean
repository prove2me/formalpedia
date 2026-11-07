-- Prove2me | Theorems.Thm_TemporalAgg_lemma_3_3
-- name    : TemporalAgg.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:01.093602+00:00
-- url     : https://prove2.me/theorems/12ed317d-337d-471e-a7bc-40a45a1370ec
-- title:
--   Lemma 3.3 — GTA performs at most q(log_{3/2} n + 5) samples
-- statement:
--   Let $(A_t)_{t\ge1}$ be any sequence of adversarial sample sets and consider any run of Greedy Temporal Aggregation against it. For every horizon $T$, if the adversary performs $q=\sum_{t=1}^{T}|A_t|$ samples, the algorithm performs at most
--
--   $$
--   \sum_{t=1}^{T}\mathrm{alg}_t\ \le\ q\,\bigl(\log_{3/2} n+5\bigr)
--   $$
--
--   samples, where $\mathrm{alg}_t$ is the number of algorithmic samples at time $t$.
--
--   This is the cost half of Theorem 1.5: aggregation needs only a logarithmic factor more samples than the adversary.
--
--   **Formalization Note** Each loop iteration on groups of sizes $a,b$ counts $a+b$ samples, including objects the adversary sampled in the same step. $\log_{3/2}$ is `Real.logb (3/2)`; at $n\le1$ the bound is $5q$.
--
--   Differences from the source:
--   - reading: if the adversary performs q samples, GTA performs at most q(log_{3/2} n + 5) samples → for every horizon T, ∑_{t=1}^{T} alg t ≤ (∑_{t=1}^{T} |A t|)·(log_{3/2} n + 5); a loop iteration on groups of sizes a, b costs a + b; time 0 is not counted; reason: the initial sampling of all objects at time 0 is neither adversarial nor algorithmic (the proof starts from 'all objects form one group of size n and hold no coins', p.17); stating it for every T covers every process length
--   - generalization: Greedy Temporal Aggregation, with the merged pair (t₁, t₂) left unspecified → every run of the nondeterministic relation IsGTARun (any choice of candidate pair at every iteration); reason: any deterministic or randomized choice rule produces such a run, so the statement specializes to each
--   - reading: while there exist time steps t₁ ≠ t₂ whose groups differ in size by at most a factor of 2 (Algorithm 1, p.16) → both groups nonempty, sizes a, b with a ≤ 2b and b ≤ 2a; reason: two empty groups would satisfy the condition forever, contradicting 'so the loop terminates' and 'the sizes of any two nonempty groups differ by more than a factor of 2' (p.16)
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), Lemma 3.3, p.16

import Mathlib
import Definitions.Def_TemporalAgg_IsGTARun

namespace TemporalAgg

/-- **Lemma 3.3** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive
Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.16). If the adversary performs `q` samples, then GTA performs at most
`q(log_{3/2} n + 5)` samples.

For every GTA run and every horizon `T`, the algorithmic samples at times `1, …, T` number at
most `(∑_{t=1}^{T} |A_t|)·(log_{3/2} n + 5)`.

**Formalization Note** `q = ∑_{t=1}^{T} |A_t|`; the sampling of all objects at time 0 is not
counted (the proof starts from "all objects form one group of size n and hold no coins", p.17).
An iteration of the loop that samples groups of sizes `a, b` costs `a + b` samples, including
objects already sampled by the adversary at the same step. The bound covers every run (every
choice of merge pairs), every `T` and every `n` (`Real.logb` is `0` at `0` and `1`). -/
theorem lemma_3_3 {n : ℕ} (A : ℕ → Finset (Fin n)) (last : ℕ → Fin n → ℕ) (alg : ℕ → ℕ)
    (hrun : IsGTARun A last alg) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (alg t : ℝ)) ≤
      (∑ t ∈ Finset.Icc 1 T, ((A t).card : ℝ)) * (Real.logb (3 / 2) n + 5) := by sorry

end TemporalAgg
