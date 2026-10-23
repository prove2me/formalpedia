-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_schmidtNumber_sum_products
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.schmidtNumber_sum_products
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:24:48.635291+00:00
-- url     : https://prove2.me/theorems/a6651984-ca76-4151-9a6d-213482cdf21c
-- title:
--   Schmidt number of a sum of product vectors
-- statement:
--   Let $n,m>0$ be integers, let $H_A=\mathbb C^n$ and $H_B=\mathbb C^m$, and let $s\ge0$ be an integer. For arbitrary vectors $x_1,\ldots,x_s\in H_A$ and $y_1,\ldots,y_s\in H_B$, write $\operatorname{SN}(v)$ for the rank of the coefficient matrix of $v$ in the canonical product basis, with $\operatorname{SN}(0)=0$. Then
--
--   $$\operatorname{SN}\!\left(\sum_{i=1}^s x_i\otimes y_i\right)\le s.$$
--
--   This bounds the Schmidt number without orthogonality, independence, nonzero-vector, or normalization assumptions.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 4, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF p.4, Lemma 1: an arbitrary sum of s product vectors has Schmidt number
at most s. The systems need not be orthogonal, independent, nonzero or normalized. -/
theorem schmidtNumber_sum_products {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : ℕ) (x : Fin s → EuclideanSpace ℂ (Fin n)) (y : Fin s → EuclideanSpace ℂ (Fin m)) :
    schmidtNumber (∑ i : Fin s, QAlgorithms.tensorVec (x i) (y i)) ≤ s := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
