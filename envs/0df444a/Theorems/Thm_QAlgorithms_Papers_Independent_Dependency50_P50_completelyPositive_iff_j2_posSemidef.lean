-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_completelyPositive_iff_j2_posSemidef
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.completelyPositive_iff_j2_posSemidef
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:29:30.329706+00:00
-- url     : https://prove2.me/theorems/9652b460-f603-46cf-9d15-d802d2e0d4db
-- title:
--   Complete positivity is equivalent to J2 positive semidefiniteness
-- statement:
--   Let $n,m>0$ be integers and let $T:M_n(\mathbb C)\to M_m(\mathbb C)$ be complex-linear. Complete positivity means that $\operatorname{id}_{M_r}\otimes T$ is positive for every positive integer $r$. For the unnormalized operator $J_2(T)=\sum_{ij}E_{ij}\otimes T(E_{ij})$ on $\mathbb C^n\otimes\mathbb C^m$, with input reference first and output second,
--
--   $$T\text{ is completely positive}\iff J_2(T)\succeq0.$$
--
--   Together with the specified $J_2$ linear bijection this identifies CP maps with positive semidefinite operators. It asserts no trace preservation, trace-one normalization, fixed input-reference marginal, or compatibility with tracing out an output environment.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 8, Corollary 2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF p.8, Corollary 2: CP iff the unnormalized, reference-first J2 matrix
is positive semidefinite. This does not impose TP, trace one or a fixed marginal. -/
theorem completelyPositive_iff_j2_posSemidef {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    QAlgorithms.Entanglement.IsCompletelyPositive T ↔ (j2 T).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
