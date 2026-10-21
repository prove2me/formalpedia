-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_hilbertSchmidt_product_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P02.hilbertSchmidt_product_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:29:19.720519+00:00
-- url     : https://prove2.me/theorems/0fb8b5c7-9cb0-44b5-a7dc-85e1a97d0ca5
-- title:
--   The trace-norm bound for every Hilbert–Schmidt product
-- statement:
--   Let $H$ be a complete real or complex Hilbert space and let $A,B$ be arbitrary Hilbert–Schmidt endomorphisms. Then
--
--   $$
--   AB\in\mathcal B_1(H),\qquad \|AB\|_1\le\|A\|_2\,\|B\|_2.
--   $$
--
--   The estimate is uniform over all such pairs, rather than confined to a selected factorization of a previously given trace-class operator.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 12, §5, unnumbered strengthening of Theorem 5.2(b)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF p.12: the product estimate holds for EVERY pair of Hilbert–Schmidt
operators, independently of the factorization chosen for a trace-class operator. -/
theorem hilbertSchmidt_product_bound (A B : H →L[F] H)
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsModulusTraceClass (A.comp B) ∧ modulusTraceNorm (A.comp B) ≤ hilbertSchmidtNorm A * hilbertSchmidtNorm B := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
