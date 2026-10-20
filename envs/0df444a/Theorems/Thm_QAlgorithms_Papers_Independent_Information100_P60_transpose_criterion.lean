-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_transpose_criterion
-- name    : QAlgorithms.Papers.Independent.Information100.P60.transpose_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:40:47.337313+00:00
-- url     : https://prove2.me/theorems/d53279a3-b816-4f71-8894-3df96c63bb90
-- title:
--   Theorem 4: scalar criterion for joint equivalence to transpose
-- statement:
--   Let $M_1,M_2$ be traceless Hermitian $3\times3$ matrices. Define $\chi(M_1,M_2)=\operatorname{Tr}(M_1^2M_2^2M_1M_2-M_2^2M_1^2M_2M_1)\in\mathbb C$. Then $$[\exists S\in U(3),\ \forall j=1,2:\ SM_jS^\dagger=M_j^T]\iff\chi(M_1,M_2)=0.$$ Moreover, if $\chi=0$, there exist $U,V\in U(3)$ such that $$M_j^T+UM_jU^\dagger+VM_jV^\dagger=0\qquad(j=1,2).$$ Transpose is in the computational basis. This scalar criterion includes its cancellation consequence.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 22, Theorem 4: scalar criterion for joint equivalence to transpose

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.21–22, Theorem 4, including the Eq.(67) consequence. -/
theorem transpose_criterion (A B : Mat (Fin 3)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htA : A.trace = 0) (htB : B.trace = 0) :
    (JointUET A B ↔ chi A B = 0) ∧ (chi A B = 0 → TransposeCancellation A B) := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
