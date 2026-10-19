-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_kPositive_iff_schmidt_blockPositive
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.kPositive_iff_schmidt_blockPositive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:27:47.085284+00:00
-- url     : https://prove2.me/theorems/9f9513fe-425d-41ae-a78f-09ffd06bbcac
-- title:
--   k-positivity is equivalent to Schmidt-number block positivity
-- statement:
--   Let $n,m,k$ be positive integers, and let $T:M_n(\mathbb C)\to M_m(\mathbb C)$ be complex-linear. Say that $T$ is $k$-positive when $\operatorname{id}_{M_k}\otimes T$ maps every positive semidefinite block matrix to a positive semidefinite block matrix. Set $J_2(T)=\sum_{ij}E_{ij}\otimes T(E_{ij})$, with input reference first, output second, and no normalization. For $v\in\mathbb C^n\otimes\mathbb C^m$, let $\operatorname{SN}(v)$ be its coefficient-matrix rank, with $\operatorname{SN}(0)=0$. Then
--
--   $$T\text{ is }k\text{-positive}\iff\forall v\in\mathbb C^n\otimes\mathbb C^m,\quad \operatorname{SN}(v)\le k\ \Longrightarrow\ \langle J_2(T)v,v\rangle\ge0.$$
--
--   The source pairing is linear in its first argument; nonnegativity includes reality. There is no unit-norm restriction on $v$ and no upper bound on $k$. This is the paper’s correspondence between $k$-positive maps and Schmidt-number block-positive operators.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 7, Theorem 3 (Main theorem), proved through PDF p.8

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF pp.7–8, Theorem 3: k-positive iff J2 is nonnegative on every vector
with Schmidt number at most k. Positive k is unrestricted above, and zero vectors
are included. Neither Hermiticity nor trace preservation is assumed in advance. -/
theorem kPositive_iff_schmidt_blockPositive {n m k : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    (∀ A : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ,
      A.PosSemidef → (QAlgorithms.idTensorSuperop (R := Fin k) T A).PosSemidef) ↔ ∀ v : Bipartite n m, schmidtNumber v ≤ k →
      0 ≤ inner ℂ v (QAlgorithms.act (j2 T) v) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
