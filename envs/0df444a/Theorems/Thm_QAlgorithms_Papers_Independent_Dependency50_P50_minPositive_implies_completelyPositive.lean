-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_minPositive_implies_completelyPositive
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.minPositive_implies_completelyPositive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:28:50.67972+00:00
-- url     : https://prove2.me/theorems/2d70d8ad-42b5-4dcf-808c-e345d02924e4
-- title:
--   Positivity at the smaller dimension implies complete positivity
-- statement:
--   Let $n,m>0$ be integers and let $T:M_n(\mathbb C)\to M_m(\mathbb C)$ be complex-linear. For a positive integer $r$, $r$-positivity means positivity of $\operatorname{id}_{M_r}\otimes T$ on every positive semidefinite block matrix. Then
--
--   $$T\text{ is }\min\{n,m\}\text{-positive}\ \Longrightarrow\ T\text{ is completely positive}.$$
--
--   Complete positivity means positivity at every finite ancilla dimension. This retains the smaller-dimension threshold, without imposing trace preservation or assuming Hermiticity separately.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 8, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF p.8, Corollary 1: positivity at the smaller dimension implies complete
positivity. The frozen CP predicate quantifies over all ancilla sizes (zero is harmless). -/
theorem minPositive_implies_completelyPositive {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    (∀ A : Matrix (Fin (min n m) × Fin n) (Fin (min n m) × Fin n) ℂ,
      A.PosSemidef →
        (QAlgorithms.idTensorSuperop (R := Fin (min n m)) T A).PosSemidef) → QAlgorithms.Entanglement.IsCompletelyPositive T := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
