-- Prove2me | Theorems.Thm_TemporalAgg_lemma_3_1
-- name    : TemporalAgg.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:04.722484+00:00
-- url     : https://prove2.me/theorems/23a9a3b0-a6ef-4f30-820b-6d9ad8753c50
-- title:
--   Lemma 3.1 — under GTA the realizations come from at most log₂ n + 1 time steps
-- statement:
--   Let $(A_t)_{t\ge1}$ be any sequence of adversarial sample sets and consider any run of Greedy Temporal Aggregation against it. At every time $t$ (including $t=0$), the realizations of all $n$ objects come from at most
--
--   $$
--   \log_2 n+1
--   $$
--
--   distinct time steps, i.e. $\#\{\mathrm{last}_t(u) : u=1,\dots,n\}\le\log_2 n+1$.
--
--   At the end of each step the nonempty group sizes differ pairwise by more than a factor of $2$, so only logarithmically many groups remain. This is the combinatorial half of the load bound.
--
--   **Formalization Note** $\log_2$ is `Real.logb 2`, with value $0$ at $n=0$ and $n=1$.
--
--   Differences from the source:
--   - reading: while there exist time steps t₁ ≠ t₂ whose groups differ in size by at most a factor of 2 (Algorithm 1, p.16) → both groups nonempty, sizes a, b with a ≤ 2b and b ≤ 2a; reason: two empty groups would satisfy the condition forever, contradicting 'so the loop terminates' and 'the sizes of any two nonempty groups differ by more than a factor of 2' (p.16)
--   - generalization: Greedy Temporal Aggregation, with the merged pair (t₁, t₂) left unspecified → every run of the nondeterministic relation IsGTARun (any choice of candidate pair at every iteration); reason: any deterministic or randomized choice rule produces such a run, so the statement specializes to each
--   - encoding: the realizations of all objects come from at most log₂ n+1 distinct time steps → the cardinality of the image of last t (a map Fin n → ℕ), cast to ℝ, is at most Real.logb 2 n + 1; reason: last t u is the time step at which the current realization of u was sampled, so the image is the set of those time steps; same instances
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), Lemma 3.1, p.16

import Mathlib
import Definitions.Def_TemporalAgg_IsGTARun

namespace TemporalAgg

/-- **Lemma 3.1** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against Adaptive
Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…, p.16). Under GTA, at every time `t`, the realizations of all objects
come from at most `log₂ n + 1` distinct time steps.

**Formalization Note** The distinct time steps are the image of `last t`. The statement covers
every GTA run (every choice of merge pairs), every `t` including `t = 0`, and every `n`
(`Real.logb 2 0 = 0`). -/
theorem lemma_3_1 {n : ℕ} (A : ℕ → Finset (Fin n)) (last : ℕ → Fin n → ℕ) (alg : ℕ → ℕ)
    (hrun : IsGTARun A last alg) (t : ℕ) :
    ((Finset.univ.image (last t)).card : ℝ) ≤ Real.logb 2 n + 1 := by sorry

end TemporalAgg
