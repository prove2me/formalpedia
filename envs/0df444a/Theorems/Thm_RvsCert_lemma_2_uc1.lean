-- Prove2me | Theorems.Thm_RvsCert_lemma_2_uc1
-- name    : RvsCert.lemma_2_uc1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:48:53.032786+00:00
-- url     : https://prove2.me/theorems/c791041a-fb73-47d5-a310-3b2f1aeb89a4
-- title:
--   Lemma 2 (second part) — $C_1(f)\le \mathrm{UC}_1(f)=O(n\log n)$
-- statement:
--   Let $f_n$ be the champion function with parameter $n$. There is a constant $A$ such that for every $n>0$,
--   $$
--   C_1(f_n)\le\mathrm{UC}_1(f_n)\qquad\text{and}\qquad \mathrm{UC}_1(f_n)\le A\,n(\log_2 n+1).
--   $$
--   Certificate sizes count input bits.
--
--   The bound on $\mathrm{UC}_1$ is the verification step of Lemmas 3 and 5, and together with Lemma 4 it separates $\mathrm{UC}_1$ from $C_0$.
--
--   Differences from the source:
--   - encoding: the function f on (X, Y) with numbers in log n bits → the bit layout `Idx n` with fixed widths wX n = ⌈log₂(2n²+1)⌉, wY n = ⌊log₂ n⌋+1, ⊥ = 0, athlete (c,b) = 1+cn+b, 0-based positions, card entry j for the j-th opponent in increasing order; reason: the paper fixes only O(log n)-bit numbers; this is one such injective encoding
--   - reading: UC1(f) = O(n log n) → UC1(f_n) ≤ A·n·(log₂ n + 1) for all n > 0; reason: asymptotic notation over the family in n, constants chosen before n; the +1 keeps the log factor positive at n = 1
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 2, p.2

import Mathlib
import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_C1
import Definitions.Def_RvsCert_UC1

namespace RvsCert

/-- **Lemma 2, second sentence** (p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "C1(f) ≤ UC1(f) = O(n log n)."
There is a constant `A` such that for every `n > 0`, `C1(f_n) ≤ UC1(f_n)` and
`UC1(f_n) ≤ A·n·(log₂ n + 1)`, where `f_n = champion n`.

**Formalization Note.** `O(n log n)` is read with `log₂ n + 1` (positive at `n = 1`), uniform
in `n`. Sizes count bits. -/
theorem lemma_2_uc1 :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      C1 (champion n) ≤ UC1 (champion n) ∧
      (UC1 (champion n) : ℝ) ≤ A * (n : ℝ) * (Real.logb 2 n + 1) := by sorry

end RvsCert
