-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_lemma_10
-- name    : RankRobustAssort.Supplement.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:36:38.048683+00:00
-- url     : https://prove2.me/theorems/1725c1d1-e090-4f9e-98d2-c8c560ea03f0
-- title:
--   Lemma 10 — under nested past assortments, $\mathcal L$ consists of tuples whose next entry repeats the previous one or is newly offered
-- statement:
--   Suppose Assumption 1 holds: the past assortments are nested, $S_1\subset\cdots\subset S_M$. With $B_m=S_m\setminus\bigcup_{m'<m}S_{m'}$ the products first offered in $S_m$,
--
--   $$
--   \mathcal L=\bigl\{(i_1,\dots,i_M)\in S_1\times\cdots\times S_M:\ i_{m+1}\in\{i_m\}\cup B_{m+1}\ \text{for each } m\in\{1,\dots,M-1\}\bigr\}.
--   $$
--
--   Here $\mathcal L$ is the set of tuples for which a single ranking makes $i_m$ the most preferred product of $S_m$ for every $m$. The lemma shows that, for nested data, the linear program (2) has exponentially many variables in $M$, and it gives the form (EC.13) of $\mathcal L$ used in the proof of Theorem 2.
--
--   **Formalization Note.** Assumption 1 is stated as inclusion $S_m\subseteq S_{m'}$ between every earlier and every later past assortment. The set equality is stated tuple by tuple.
--
--   Differences from the source:
--   - generalization: Assumption 1, printed as the strict chain $S_1\subset\cdots\subset S_M$ (the prose calls each assortment "a subset of the subsequent assortment") → $S_m\subseteq S_{m'}$ for $m<m'$; reason: the strict chain implies it, so both readings of the printed symbol are covered; the lemma also holds when two consecutive past assortments coincide, since then $B_{m+1}=\emptyset$ and the common top product repeats
--   - generalization: the §5 standing assumption $\bigcup_{m}S_m=\mathcal N_0$ (Remark 3, p.16) → not assumed; reason: the proof (Appendix I.1) never uses it; every instance satisfying it is covered
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only the revenues, the past assortments, rankings, tuples and $\mathcal L$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Assumption 1, equation (3) and Lemma 10, p.19

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Supplement_Bset

namespace RankRobustAssort.Supplement

/-- **Lemma 10.** If Assumption 1 holds (the past assortments are nested, `S₁ ⊂ ⋯ ⊂ S_M`; stated with `⊆`), then
`ℒ = {(i₁,…,i_M) ∈ S₁ × ⋯ × S_M : for each m ∈ {1,…,M−1}, i_{m+1} ∈ {i_m} ∪ B_{m+1}}`.

Sturt, arXiv:2112.05010v4, Assumption 1 and Lemma 10, p.19; `B_m`, (3), p.19.

Formalization Note: Assumption 1 is `hnest`: inclusion `P.S m ⊆ P.S m'` for all Lean
indices `m < m'`. The printed chain `S₁ ⊂ ⋯ ⊂ S_M` (strict, while the surrounding prose says "each
assortment is a subset of the subsequent assortment") implies it, so the statement covers both
readings; the lemma also holds when consecutive past assortments coincide (then `B_{m+1} = ∅`). Tuples are
`t : Fin M → Fin (n+1)`, Lean index `k` = paper index `k + 1`, so "`m ∈ {1,…,M−1}`, `i_{m+1}`" is
"`k` with `k + 1 < M`, `t (k+1)`". The §5 standing assumption `⋃_m S_m = 𝒩₀` (Remark 3, p.16) is
not assumed. The set equality is stated pointwise for every tuple. -/
theorem lemma_10 {n M : ℕ} (P : Problem n M)
    (hnest : ∀ m m' : Fin M, m < m' → P.S m ⊆ P.S m') (t : Fin M → Fin (n + 1)) :
    InL P t ↔
      (∀ m, t m ∈ P.S m) ∧
      ∀ (k : ℕ) (hk : k + 1 < M),
        t ⟨k + 1, hk⟩ = t ⟨k, Nat.lt_of_succ_lt hk⟩ ∨ t ⟨k + 1, hk⟩ ∈ Bset P ⟨k + 1, hk⟩ := by sorry

end RankRobustAssort.Supplement
