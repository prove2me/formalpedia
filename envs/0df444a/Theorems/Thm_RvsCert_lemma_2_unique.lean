-- Prove2me | Theorems.Thm_RvsCert_lemma_2_unique
-- name    : RvsCert.lemma_2_unique
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:46:26.544195+00:00
-- url     : https://prove2.me/theorems/f00cae9e-3ec0-4e87-9859-34653fc210a0
-- title:
--   Lemma 2 (first part) — at most one champion
-- statement:
--   For every $n>0$ and every input $(X,Y)$ of the champion function, if athletes $a$ and $a'$ are both champions of $(X,Y)$, then $a=a'$.
--
--   This is what makes the 1-certificates of Lemma 2 unambiguous and makes the tournament in Lemmas 3 and 5 meaningful.
--
--   Differences from the source:
--   - encoding: the function f on (X, Y) with numbers in log n bits → the bit layout `Idx n` with fixed widths wX n = ⌈log₂(2n²+1)⌉, wY n = ⌊log₂ n⌋+1, ⊥ = 0, athlete (c,b) = 1+cn+b, 0-based positions, card entry j for the j-th opponent in increasing order; reason: the paper fixes only O(log n)-bit numbers; this is one such injective encoding
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 2, p.2

import Mathlib
import Definitions.Def_RvsCert_IsChampion

namespace RvsCert

/-- **Lemma 2, first sentence** (p.2 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "There is at most one
champion." For every `n > 0` and every input `x`, two champions of `x` are the same athlete. -/
theorem lemma_2_unique (n : ℕ) (hn : 0 < n) (x : Idx n → Bool) (a a' : Fin (2 * n) × Fin n)
    (ha : IsChampion n x a) (ha' : IsChampion n x a') : a = a' := by sorry

end RvsCert
