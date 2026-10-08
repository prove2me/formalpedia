-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tightP_sum_eq_rows
-- name    : RevenueOrdered.Tightness.tightP_sum_eq_rows
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:17:04.183616+00:00
-- url     : https://prove2.me/theorems/77a45a4b-9b6e-4d4b-9a32-27f0b6b4c755
-- title:
--   (8), p. 10 — the purchase probability of the tight instance is the sum of $\varepsilon^i$ over nonempty rows
-- statement:
--   Let $\mathcal P$ be the system of choice probabilities of the tight instance, with $0<\varepsilon\le\tfrac12$. For $S\subseteq\mathcal C$ and $i\in[k]$ let $S_i=\{(i,j): j\in[i],\ (i,j)\in S\}$ be the $i$-th row of $S$. For $S\subseteq S'\subseteq\mathcal C$,
--   $$
--   \sum_{(i,j)\in S}\mathcal P((i,j),S)=\sum_{i\in[k]}\sum_{(i,j)\in S_i}\mathcal P((i,j),S_i)=\sum_{i\in[k],\,S_i\ne\emptyset}\varepsilon^i\le\sum_{i\in[k],\,S'_i\ne\emptyset}\varepsilon^i=\sum_{(i,j)\in S'}\mathcal P((i,j),S').
--   $$
--
--   The purchase probability of a set depends only on which rows it meets, and it does not decrease when the set grows.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4, display (8)

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- Display (8) (p. 10): with `S_i` the row `i` of `S`, for `S ⊆ S' ⊆ 𝒞`,
`∑_{(i,j)∈S} 𝒫((i,j),S) = ∑_{i∈[k]} ∑_{(i,j)∈S_i} 𝒫((i,j),S_i) = ∑_{i∈[k], S_i≠∅} ε^i
 ⩽ ∑_{i∈[k], S'_i≠∅} ε^i = ∑_{(i,j)∈S'} 𝒫((i,j),S')`. -/
theorem tightP_sum_eq_rows (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S S' : Finset (TightProduct k)) (hSS' : S ⊆ S') :
    ∑ x ∈ S, tightP k ε x S =
        ∑ i ∈ Finset.Icc 1 k, ∑ x ∈ row S i, tightP k ε x (row S i) ∧
      ∑ i ∈ Finset.Icc 1 k, ∑ x ∈ row S i, tightP k ε x (row S i) =
        ∑ i ∈ (Finset.Icc 1 k).filter (fun i => (row S i).Nonempty), ε ^ i ∧
      ∑ i ∈ (Finset.Icc 1 k).filter (fun i => (row S i).Nonempty), ε ^ i ≤
        ∑ i ∈ (Finset.Icc 1 k).filter (fun i => (row S' i).Nonempty), ε ^ i ∧
      ∑ i ∈ (Finset.Icc 1 k).filter (fun i => (row S' i).Nonempty), ε ^ i =
        ∑ x ∈ S', tightP k ε x S' := by sorry

end RevenueOrdered.Tightness
