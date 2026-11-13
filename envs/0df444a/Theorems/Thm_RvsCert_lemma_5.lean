-- Prove2me | Theorems.Thm_RvsCert_lemma_5
-- name    : RvsCert.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:48:31.72775+00:00
-- url     : https://prove2.me/theorems/9f0c1259-d458-4606-aae5-ff381cb27ac6
-- title:
--   Lemma 5 — $Q(f)=\tilde O(\sqrt n)$
-- statement:
--   Let $f_n$ be the champion function. There are constants $A$ and $k$ such that for every $n>0$ there is a natural number $T$ with
--   $$
--   Q(f_n)\le T\le A\sqrt n\,(\log_2 n+1)^k,
--   $$
--   where $Q$ is the bounded-error quantum query complexity (error at most $1/3$ on every input, standard bit queries).
--
--   Differences from the source:
--   - encoding: the function f on (X, Y) with numbers in log n bits → the bit layout `Idx n` with fixed widths wX n = ⌈log₂(2n²+1)⌉, wY n = ⌊log₂ n⌋+1, ⊥ = 0, athlete (c,b) = 1+cn+b, 0-based positions, card entry j for the j-th opponent in increasing order; reason: the paper fixes only O(log n)-bit numbers; this is one such injective encoding
--   - reading: Q(f) = Õ(√n) → ∃ T : ℕ, quantQC f_n ≤ T ∧ T ≤ A·√n·(log₂ n + 1)^k, for all n > 0; reason: asymptotic notation over the family in n, constants chosen before n; the +1 keeps the log factor positive at n = 1
--   - encoding: Q(f), bounded-error quantum query complexity → quantQC, an infimum in ℕ∞ over T-query algorithms with finite workspace and success ≥ 2/3 on every input; reason: the standard [BdW02] notion; ℕ∞ keeps the bound non-vacuous
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 5, p.3 (proof pp.3–5)

import Mathlib
import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_quantQC

namespace RvsCert

/-- **Lemma 5** (p.3 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "There is an even faster quantum algorithm:
Q(f) = Õ(√n)." There are constants `A, k` such that for every `n > 0` the bounded-error
(error `1/3` on every input) quantum query complexity of `champion n` with standard bit queries
is at most `A·√n·(log₂ n + 1)^k`. -/
theorem lemma_5 :
    ∃ (A : ℝ) (k : ℕ), ∀ n : ℕ, 0 < n → ∃ T : ℕ, quantQC (champion n) ≤ T ∧
      (T : ℝ) ≤ A * Real.sqrt n * (Real.logb 2 n + 1) ^ k := by sorry

end RvsCert
