-- Prove2me | Theorems.Thm_RvsCert_lemma_3_first_stage
-- name    : RvsCert.lemma_3_first_stage
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:46:39.493173+00:00
-- url     : https://prove2.me/theorems/43b2ff03-6289-4486-9c81-37e4b5826cbc
-- title:
--   Proof of Lemma 3, first stage — a champion is first in at least half of its races
-- statement:
--   Let $n>0$ and let $a=(c,b)$ be a champion of the input $(X,Y)$. Among the $2n-1$ races of $a$, the number of races whose result list holds $a$ at the first position is at least half of $2n-1$:
--   $$
--   2\cdot\#\{j : X_{r_j}[0]=a\}\ \ge\ 2n-1,
--   $$
--   where $r_j$ is the $j$-th race of $c$.
--
--   This is why sampling the winners of a constant number of races per country finds the champion with constant probability.
--
--   Differences from the source:
--   - encoding: the function f on (X, Y) with numbers in log n bits → the bit layout `Idx n` with fixed widths wX n = ⌈log₂(2n²+1)⌉, wY n = ⌊log₂ n⌋+1, ⊥ = 0, athlete (c,b) = 1+cn+b, 0-based positions, card entry j for the j-th opponent in increasing order; reason: the paper fixes only O(log n)-bit numbers; this is one such injective encoding
--   - reading: in the first position in at least half of their races → 2·#{j : race entry 0 of race j decodes to a} ≥ 2n − 1; reason: 'at least half' of 2n − 1 races, written without division
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, proof of Lemma 3, first stage, p.3

import Mathlib
import Definitions.Def_RvsCert_IsChampion

namespace RvsCert

/-- **Proof of Lemma 3, first stage** (p.3 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "if there is a champion,
this athlete must be in the first position in at least half of their races, since they participate
in 2n − 1 races and only < n non-athletes are allowed to finish ahead of the champion in total."
If `(c, b)` is a champion of `x`, then the number of its races `j` whose result list holds
`(c, b)` at the first position is at least half of `2n − 1`. -/
theorem lemma_3_first_stage (n : ℕ) (hn : 0 < n) (x : Idx n → Bool) (a : Fin (2 * n) × Fin n)
    (ha : IsChampion n x a) :
    2 * (Finset.univ.filter fun j : Fin (2 * n - 1) =>
        raceEntry n x (raceOf a.1 j) ⟨0, hn⟩ = athleteCode n a).card ≥ 2 * n - 1 := by sorry

end RvsCert
