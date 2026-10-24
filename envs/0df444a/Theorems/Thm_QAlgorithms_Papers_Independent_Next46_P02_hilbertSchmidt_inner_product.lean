-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_hilbertSchmidt_inner_product
-- name    : QAlgorithms.Papers.Independent.Next46.P02.hilbertSchmidt_inner_product
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:32:00.617454+00:00
-- url     : https://prove2.me/theorems/ba2162fe-a423-46b7-9088-06c7a8f6c700
-- title:
--   The Hilbert–Schmidt inner product and Schwarz inequality
-- statement:
--   Let $H$ be a complete real or complex Hilbert space. For Hilbert–Schmidt endomorphisms $T,S$, the source’s first-linear inner product is
--
--   $$
--   \langle T;S\rangle_2=\operatorname{tr}(S^*T)
--   =\sum_i\langle Te_i;Se_i\rangle.
--   $$
--
--   The series converges for every complete orthonormal basis. This form is an inner product inducing the Hilbert–Schmidt norm, with all sesquilinearity, conjugate-symmetry and definiteness axioms. It satisfies
--
--   $$
--   |\langle T;S\rangle_2|\le\|T\|_2\|S\|_2,\qquad
--   \operatorname{tr}(T^*T)=\|T\|_2^2.
--   $$
--
--   In Lean’s first-conjugate-linear convention the inner product with arguments $S,T$ is $\operatorname{tr}(S^*T)$. This reversal preserves the source formula exactly.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 16, §5, Remark 5.6: Hilbert–Schmidt inner product and Schwarz bound

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF pp.16–17, Remark 5.6: the full Hilbert–Schmidt inner product, its
convergent basis series, norm identity, and Schwarz inequality. -/
theorem hilbertSchmidt_inner_product :
    InnerProductOn (IsHilbertSchmidt (F := F) (H := H)) hilbertSchmidtNorm hilbertSchmidtInner ∧
    (∀ {I : Type*} (b : HilbertBasis I F H) (S T : H →L[F] H),
      IsHilbertSchmidt S → IsHilbertSchmidt T →
      HasSum (fun i => inner F (S (b i)) (T (b i))) (hilbertSchmidtInner S T) ∧
      ‖hilbertSchmidtInner S T‖ ≤ hilbertSchmidtNorm S * hilbertSchmidtNorm T) ∧
    (∀ T : H →L[F] H, IsHilbertSchmidt T →
      basisOperatorTrace ((ContinuousLinearMap.adjoint T).comp T) = (hilbertSchmidtNorm T ^ 2 : F)) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
