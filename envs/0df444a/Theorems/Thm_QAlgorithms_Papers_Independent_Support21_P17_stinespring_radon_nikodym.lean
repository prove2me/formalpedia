-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_stinespring_radon_nikodym
-- name    : QAlgorithms.Papers.Independent.Support21.P17.stinespring_radon_nikodym
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:38:36.636147+00:00
-- url     : https://prove2.me/theorems/6f9c27c0-4e9c-469c-94b9-b4c7421a8a1c
-- title:
--   Stinespring Radon–Nikodym theorem
-- statement:
--   Let $\mathcal A$ be a unital complex C*-algebra with a specified faithful concrete realization on a separable Hilbert space, and let $S,T:\mathcal A\to B(H)$ be normal complex-linear completely positive maps. Fix a minimal Stinespring dilation $T(a)=V^*\pi(a)V$ on a complex separable Hilbert space $K$, where minimality means that the closed linear span of $\pi(\mathcal A)VH$ is $K$. Complete domination $S\le T$ means that $T-S$ is completely positive. Then
--
--   $$S\le T\iff\exists F\in\pi(\mathcal A)',\quad 0\le F\le I_K,\qquad S(a)=V^*\pi(a)FV=V^*\sqrt F\,\pi(a)\sqrt F\,V\quad(a\in\mathcal A).$$
--
--   For this $F$, every bounded $Y\in\pi(\mathcal A)'$ satisfying $S(a)=V^*\pi(a)YV$ for all $a$ equals $F$, whether or not $Y$ is positive. This is the complete classification of the CP order interval below $T$.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 7, Theorem 3.1: Stinespring Radon–Nikodym theorem (seed resolved from abstract)

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Theorem 3.1, PDF pp.7–8: existence, converse, symmetric square-root form, and
strong uniqueness among all commutant operators, with no positivity assumption on Y.
The uniqueness proof's reference to the dilation of S is read as the fixed dilation of T. -/
theorem stinespring_radon_nikodym {A : Type*} [CStarAlgebra A]
    (G H K : SeparableHilbertSpace) (rho : A →⋆ₐ[ℂ] HilbertEndomorphism G) (h_rho : Function.Injective rho)
    (T : A →ₗ[ℂ] HilbertEndomorphism H) (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hT : IsNormalCP rho T) (h_dilation : ∀ a, T a = compress V (pi a))
    (h_minimal : IsMinimal pi V) (S : A →ₗ[ℂ] HilbertEndomorphism H) (hS : IsNormalCP rho S) :
    CompletelyDominated S T ↔ ∃ F : HilbertEndomorphism K, CommutesWithRepresentation pi F ∧ PositiveContraction F ∧
      (∀ a, S a = compress V ((pi a).comp F) ∧
        S a = compress V ((cfc Real.sqrt F).comp ((pi a).comp (cfc Real.sqrt F)))) ∧
      ∀ Y : HilbertEndomorphism K, CommutesWithRepresentation pi Y → (∀ a, S a = compress V ((pi a).comp Y)) → Y = F := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
