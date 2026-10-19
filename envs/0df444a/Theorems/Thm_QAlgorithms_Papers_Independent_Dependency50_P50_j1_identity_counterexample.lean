-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_j1_identity_counterexample
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.j1_identity_counterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:28:13.016502+00:00
-- url     : https://prove2.me/theorems/be47627d-13e7-416f-9f11-69cafd3f07e8
-- title:
--   The two-dimensional identity disproves the J1 analogue
-- statement:
--   Let $T=\operatorname{id}_{M_2(\mathbb C)}$, let $e_1,e_2$ be the standard basis of $\mathbb C^2$, and set $v=e_1\otimes e_2-e_2\otimes e_1\in\mathbb C^2\otimes\mathbb C^2$. Define $J_1(T)=\sum_{ij}E_{ij}^*\otimes T(E_{ij})$. The map $T$ is completely positive, and
--
--   $$J_1(T)v=-v,\qquad \operatorname{SN}(v)=2,\qquad \langle J_1(T)v,v\rangle=-2<0.$$
--
--   Consequently, $J_1(T)$ fails nonnegativity on all vectors of Schmidt number at most $2$, despite complete positivity of $T$. This disproves the analogue of Theorem 3 with $J_1$ replacing $J_2$.
--
--   **Formalization Note** The printed membership $v\in\mathbb C^2$ is corrected to the tensor-product space forced by the displayed vector. The source vector is not normalized.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 8, §V, counterexample after Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF p.8, §V: the completely positive two-dimensional identity is a
counterexample to replacing J2 with J1 in Theorem 3. Printed v in C^2 is corrected
to C^2 tensor C^2, as forced by the displayed vector. No normalization is imposed. -/
theorem j1_identity_counterexample :
    QAlgorithms.Entanglement.IsCompletelyPositive (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)) ∧
      QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) antisymmetricVector =
        (-1 : ℂ) • antisymmetricVector ∧
      schmidtNumber antisymmetricVector = 2 ∧
      inner ℂ antisymmetricVector
        (QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) antisymmetricVector) = (-2 : ℂ) ∧
      ¬ (∀ v : Bipartite 2 2, schmidtNumber v ≤ 2 →
        0 ≤ inner ℂ v (QAlgorithms.act (j1 (LinearMap.id : (Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ))) v)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
