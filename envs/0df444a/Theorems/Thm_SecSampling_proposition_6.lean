-- Prove2me | Theorems.Thm_SecSampling_proposition_6
-- name    : SecSampling.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:21.283817+00:00
-- url     : https://prove2.me/theorems/5407387d-ad05-420e-904f-a354c1c7feee
-- title:
--   Proposition 6 — the colored last zero problem as an instance of AOSp with known $n$
-- statement:
--   Let $p\in(0,1)$ and let $A$ be an ordinal, possibly randomized AOSp algorithm that knows $n$. There is a colored strategy $B$ such that for all $m\le n$ and all distinct values $v_1,\dots,v_n$ with
--   $$0<v_1<v_2<\dots<v_m\quad\text{and}\quad v_{m+1},\dots,v_n<0,$$
--   presented in index order, the success probability of $A$ in AOSp is at most the performance of $B$ in the colored last zero problem on $(m,n)$.
--
--   Hence any negative result for the colored last zero problem holds for AOSp, even for players who know $n$. The strategy $B$ is constructed from $A$ alone and does not know $m$.
--
--   Differences from the source:
--   - reading: the colored last zero problem is equivalent to a specific instance of AOSp with known size n → for every ordinal AOSp algorithm A there is a colored strategy B, chosen before m, n and the values, with AOSp success probability of A ≤ colored performance of B on (m, n); reason: the paper gives "equivalent" no formal meaning; its proof and the "Therefore" clause use exactly this transfer, and the reverse simulation would need an AOSp player to know the numbers of red and blue samples separately
--   - encoding: an ordinal algorithm, deciding on the relative rankings of the values seen so far plus possibly external randomness (p.2) → a function A n |S| h ∈ [0,1], the stopping probability given n, the number of samples and the ordinal history h (for each online element so far: the number of samples above it and of earlier online elements above it); reason: behavioural randomization is equivalent to any external randomness under perfect recall (Kuhn); the pairs determine exactly the relative order of the samples and the online elements seen so far
--   - reading: the player wins if she stops on the last red 0 of the sequence (Definition 3) → an instance with no red 0 is won by every strategy; reason: the page leaves this case open; it is the convention of p.2, and the inequality with AOSp needs it because there the player can still win among the blue elements
--   - encoding: the remaining n − m take arbitrary negative values → negative and pairwise distinct values (Function.Injective v); reason: the paper presupposes distinct values, so that the maximum is unique
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Proposition 6, p.26 (PDF p.27), with its proof

import Mathlib
import Definitions.Def_SecSampling_AOSp
import Definitions.Def_SecSampling_ColoredLastZero

namespace SecSampling

/-- **Proposition 6** (arXiv:2011.07869v1, p.26). The colored last zero problem is equivalent to a
specific instance of AOSp with known size `n`, so negative results transfer: for every ordinal,
possibly randomized AOSp algorithm `A` (which knows `n`) there is a colored strategy `B` such that
on every instance whose first `m` elements carry positive strictly increasing values and whose
remaining `n − m` elements carry negative values, presented in index order, the success
probability of `A` is at most the performance of `B` on `(m, n)`.

**Formalization Note.** `B` is chosen before `m`, `n` and the values, so it does not know `m`.
The negative values are arbitrary (distinct), as in the proof on p.26. -/
theorem proposition_6 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (A : Algorithm) (hA : IsAlgorithm A) :
    ∃ B : ColStrategy, IsColStrategy B ∧
      ∀ (m n : ℕ), m ≤ n → ∀ v : Fin n → ℝ, Function.Injective v →
        (∀ i j : Fin n, i < j → (j : ℕ) < m → v i < v j) →
        (∀ i : Fin n, (i : ℕ) < m → 0 < v i) →
        (∀ i : Fin n, m ≤ (i : ℕ) → v i < 0) →
        winProb p A v (indexOrder n) ≤ perfColored p B m n := by sorry

end SecSampling
