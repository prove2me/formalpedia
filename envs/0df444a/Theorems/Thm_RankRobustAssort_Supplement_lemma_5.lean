-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_lemma_5
-- name    : RankRobustAssort.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:36:05.270035+00:00
-- url     : https://prove2.me/theorems/00873c36-f094-4380-b962-ed888ef79c3c
-- title:
--   Lemma 5 — for reverse revenue-ordered past assortments, $\widehat{\mathcal S}$ is the set of assortments containing $0$ and $n$
-- statement:
--   Let the past assortments be the reverse revenue-ordered ones, $\mathcal M=\widetilde{\mathcal S}$ ($S_1=\{0,n\}$, $S_m=\{0,\dots,m-1,n\}$ for $m=2,\dots,n$), and let $\widehat{\mathcal S}$ be the collection of assortments that are revenue-ordered relative to the past assortments. Then
--
--   $$
--   \widehat{\mathcal S}=\{S\subseteq\mathcal N_0:\ \{0,n\}\subseteq S\}.
--   $$
--
--   Hence $|\widehat{\mathcal S}|=2^{M-2}$ grows exponentially in the number of past assortments; Theorem 2 shows that none of these assortments can be discarded.
--
--   Differences from the source:
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only the revenues, the past assortments, rankings, tuples and $\mathcal L$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
--   - generalization: $n\ge1$ (Definition 1 needs $n$ to be a product) → every $n\ge0$; reason: at $n=0$ there are no past assortments and both sides are $\{S:0\in S\}$; for $n\ge1$ it is the paper's statement
--   - encoding: $\mathcal M=\widetilde{\mathcal S}$ → the past assortments of the instance equal the family $S_1,\dots,S_n$ of Definition 1, indexed $0,\dots,n-1$; reason: same instances
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma 5, p.14

import Mathlib
import Definitions.Def_RankRobustAssort_SHat
import Definitions.Def_RankRobustAssort_Supplement_revPast

namespace RankRobustAssort.Supplement

/-- **Lemma 5.** If `ℳ = S̃`, then `Ŝ = {S ⊆ 𝒩₀ : {0,n} ⊆ S}`.

Sturt, arXiv:2112.05010v4, Lemma 5, p.14.

Formalization Note: `ℳ = S̃` is `P.S = revPast n` (so `M = n`); the revenues, data, radius and
norm of `P` are arbitrary, since `Ŝ` depends only on the revenues and the past assortments. The
product `n` is `Fin.last n`. -/
theorem lemma_5 {n : ℕ} (P : Problem n n) (hS : P.S = revPast n) :
    SHat P = {S | 0 ∈ S ∧ Fin.last n ∈ S} := by sorry

end RankRobustAssort.Supplement
