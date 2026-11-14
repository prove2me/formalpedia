-- Prove2me | Theorems.Thm_RvsCert_lemma_3
-- name    : RvsCert.lemma_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:48:33.903129+00:00
-- url     : https://prove2.me/theorems/7694796c-2a10-48cf-834f-e86d98be67fc
-- title:
--   Lemma 3 — $R(f)=O(n\log n)$
-- statement:
--   Let $f_n$ be the champion function. There is a constant $A$ such that for every $n>0$ there is a natural number $T$ with
--   $$
--   R(f_n)\le T\le A\,n(\log_2 n+1),
--   $$
--   where $R$ is the bounded-error randomized query complexity (error at most $1/3$ on every input, worst-case number of bit queries).
--
--   Differences from the source:
--   - encoding: the function f on (X, Y) with numbers in log n bits → the bit layout `Idx n` with fixed widths wX n = ⌈log₂(2n²+1)⌉, wY n = ⌊log₂ n⌋+1, ⊥ = 0, athlete (c,b) = 1+cn+b, 0-based positions, card entry j for the j-th opponent in increasing order; reason: the paper fixes only O(log n)-bit numbers; this is one such injective encoding
--   - reading: R(f) = O(n log n) → ∃ T : ℕ, randQC f_n ≤ T ∧ T ≤ A·n·(log₂ n + 1), for all n > 0; reason: asymptotic notation over the family in n, constants chosen before n; the +1 keeps the log factor positive at n = 1
--   - encoding: R(f), bounded-error randomized query complexity → randQC, an infimum in ℕ∞ with success probability ≥ 2/3 on every input and worst-case query count; reason: the standard [BdW02] notion; ℕ∞ keeps the bound non-vacuous
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 3, p.3

import Mathlib
import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_randQC

namespace RvsCert

/-- **Lemma 3** (p.3 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "There is a fast randomized algorithm:
R(f) = O(n log n)." There is a constant `A` such that for every `n > 0` the bounded-error
(error `1/3` on every input) randomized query complexity of `champion n`, counted in bit
queries, is at most `A·n·(log₂ n + 1)`.

**Formalization Note.** The upper bound is stated as `∃ T : ℕ, randQC f ≤ T ∧ T ≤ …`, so an
infeasible (`⊤`) value is excluded; `A` is chosen before `n`. -/
theorem lemma_3 :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n → ∃ T : ℕ, randQC (champion n) ≤ T ∧
      (T : ℝ) ≤ A * (n : ℝ) * (Real.logb 2 n + 1) := by sorry

end RvsCert
