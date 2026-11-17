-- Prove2me | Theorems.Thm_TemporalAgg_Supplement_theorem_B_1
-- name    : TemporalAgg.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:21:01.645875+00:00
-- url     : https://prove2.me/theorems/775ff9cd-26f6-4e08-82ad-b5d912d78683
-- title:
--   Theorem B.1 — proactive resampling is not competitive with the target load
-- statement:
--   Consider the job–machine setting under proactive resampling: an adaptive adversary deletes one machine per time step, which deletes the routines containing it; jobs that used it are reassigned to a uniformly random remaining routine (adversarial samples), and every job with an adversarial sample at time $s$ is also reassigned uniformly at random at times $s+2^i$, $i\ge0$.
--
--   There are a constant $C>0$, a threshold $n_0$ and, for every number $n$ of jobs, an instance (machines, routines, a machine $x^\star$, a horizon $T$ and an adaptive deletion sequence) such that for every $n\ge n_0$ the instance is valid, $T\le Cn^3$, and
--
--   $$
--   \mathbb E\big[\mathrm{load}_T(x^\star)\big]\ \ge\ \sqrt n ,
--   $$
--
--   while for every constant $c>0$ there is $n_1$ such that for all $n\ge n_1$
--
--   $$
--   \Pr\big[\ \mathrm{target}_t(x^\star)\le 4\ \text{ for all } t\le T\ \big]\ \ge\ 1-n^{-c}.
--   $$
--
--   Bhattacharya, Saranurak and Sukprasert bounded $\mathrm{load}_t(x)$ by $\mathrm{target}_t(x)$ up to polylogarithmic factors under proactive resampling; this instance shows the load can exceed the target by a polynomial factor, because the adversary changes the routine sets between samples (temporal selection).
--
--   **Formalization Note** Probabilities and expectations are over independent uniform random numbers $\xi_{j,s}$, $s\le T$, driving the (re)assignments; see the definition of the setting.
--
--   Differences from the source:
--   - reading: T = O(n³); w.h.p. → ∃ C and n₀ with T ≤ C·n³ for n ≥ n₀; for every c > 0 there is n₁ with probability ≥ 1 − n^{−c} for n ≥ n₁, for the same instances; reason: Preliminaries, p.14: w.h.p. is probability ≥ 1 − n^{−c} for a c that can be made arbitrarily large; fixing the instances before c is the strongest reading
--   - reading: a configuration of n jobs (the proof arranges the jobs in √n batches of size √n) → every n ≥ n₀, √n the real square root; reason: the theorem is stated for n jobs, not only perfect squares; the proof with ⌊√n⌋ routines per pretrimmed job and batches of size ⌊√n⌋ gives the same bounds for large n
--   - encoding: adaptive adversarial sequence of machine deletions; uniformly random routines → deterministic adversary reading the assignment history, one fresh machine per step on every history (JMValid); picks driven by independent uniform numbers in {0,…,|routines|!−1}; reason: for a deterministic adversary this history is the whole history; the driven picks are uniform among the current routines
--   - encoding: every job is assigned to exactly one of its routines at all times → validity: every job keeps at least one routine at all t ≤ T on every history; reason: the setting presupposes it; the construction never empties a job
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), App. B.2, p.38, Theorem B.1 (proof pp.38–39)

import Mathlib
import Definitions.Def_NoSignalPA_uniformExp
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_TemporalAgg_Supplement_jmState

namespace TemporalAgg.Supplement

/-- **Theorem B.1** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against
Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.38;
proved on pp.38–39).

There exists a configuration of `n` jobs, machines, and routines, along with an adaptive
adversarial sequence of `T = O(n³)` machine deletions, such that under proactive resampling, there
is a machine `x⋆` such that, w.h.p., `target_t(x⋆) ≤ 4` for all `t ≤ T`, but
`𝔼[load_T(x⋆)] ≥ √n`.

**Formalization Note** `T = O(n³)` is read with an absolute constant `C` and a threshold `n₀`;
the instance `I n` (machines, routines, `x⋆`, `T`, adaptive deletion rule) is chosen for every `n`
once and for all. "W.h.p." is the paper's (Preliminaries, p.14): probability at least `1 − n^{−c}`
for every constant `c > 0`, for all sufficiently large `n`; here the same instances work for every
`c`, which is the strongest reading. The constants `4` and `√n` are exact. Validity (`JMValid`):
one fresh machine deletion per step and no job ever loses all its routines, on every history.
The process is `jmState` (time-0 uniform assignment, forced reassignments, proactive resampling at
`s + 2ⁱ`). Probabilities and expectations are over the first `T + 1` steps' randomness, uniform on
`Fin n → Fin (T+1) → Fin N` with `N = |routines|!`. -/
theorem theorem_B_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∃ I : (n : ℕ) → JMInstance n,
      (∀ n ≥ n₀, JMValid (I n) ∧ ((I n).T : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
        Real.sqrt n ≤ NoSignalPA.uniformExp
          (fun η : Fin n → Fin ((I n).T + 1) → Fin (Nat.factorial (I n).routines.card) =>
            (jmLoad (I n) (jmRand η) (I n).T (I n).xstar : ℝ))) ∧
      ∀ c : ℝ, 0 < c → ∃ n₁ : ℕ, ∀ n ≥ n₁,
        1 - (n : ℝ) ^ (-c) ≤ PunctSketch.coinProb
          (fun η : Fin n → Fin ((I n).T + 1) → Fin (Nat.factorial (I n).routines.card) =>
            ∀ t ≤ (I n).T, jmTarget (I n) (jmRand η) t (I n).xstar ≤ 4) := by sorry

end TemporalAgg.Supplement
