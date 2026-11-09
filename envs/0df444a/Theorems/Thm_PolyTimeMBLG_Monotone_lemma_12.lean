-- Prove2me | Theorems.Thm_PolyTimeMBLG_Monotone_lemma_12
-- name    : PolyTimeMBLG.Monotone.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:19.57336+00:00
-- url     : https://prove2.me/theorems/6e298fb4-b587-4ba5-b93b-846f85a82ae7
-- title:
--   Lemma 12 — exponential steps in the game with numbers
-- statement:
--   Consider the game with numbers: the board is a finite multiset of natural numbers that initially holds any number of zeros; in each step one occurrence of the minimum of the (nonempty) board is increased by $1$, giving the intermediate board, after which a nonempty sub-multiset is erased and any number of zeros is added.
--
--   Let $k\ge1$. In every play, if the number $k$ is on the intermediate board $I_t$ of step $t$ (right after the increment of step $t$, before the erasure), then
--   $$t\ \ge\ 2^{k-1}.$$
--   In particular, the minimal number of steps for the number $k$ to appear on the board is at least $2^{k-1}$.
--
--   In the proof of Theorem 11 the board holds the numbers of times each maximal unmarked word has been output at crucial moments, and there are at most $2^n$ crucial moments; the lemma therefore shows that no word is output at crucial moments more than $n+1$ times.
--
--   **Formalization Note** The source calls the board value $n$; here it is $k$, to keep $n$ for the word length. Any $k\ge1$ on a board $B_t$ after step $t$ is also on $I_t$ (the zeros added are not $k$), so the statement covers appearance on the boards as well. The play has an arbitrary finite number $T$ of steps and $1\le t\le T$.
--
--   Differences from the source:
--   - reading: "the minimal number of steps for a number n to appear on the board" → every occurrence of $k\ge1$ on the intermediate board $I_t$ of step $t$ (after the increment, before the erasure) forces $t\ge2^{k-1}$; reason: the source does not fix the moment within a step at which a number "appears"; the intermediate board is the stronger reading, because every $k\ge1$ on the board after step $t$ is also on $I_t$, and it is the reading the proof's coin argument supports.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Lemma 12, p. 8 (the game with numbers is defined just before it on p. 8). PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_NumberGame

namespace PolyTimeMBLG.Monotone

/-- Lemma 12 (p. 8): if a number `k ≥ 1` is on the board right after the increment of step `t`
of a legal play (before the erasure), then `t ≥ 2^(k-1)`. -/
theorem lemma_12 (T : ℕ) (board inter : ℕ → Multiset ℕ) (hplay : IsPlay T board inter)
    (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) (htT : t ≤ T) (hkt : k ∈ inter t) :
    2 ^ (k - 1) ≤ t := by sorry

end PolyTimeMBLG.Monotone
