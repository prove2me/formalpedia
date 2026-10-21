-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_finite_cp_decomposition
-- name    : QAlgorithms.Papers.Independent.Support21.P17.finite_cp_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:41:35.428992+00:00
-- url     : https://prove2.me/theorems/e6be74fb-8082-49bb-959d-9b8bada222b7
-- title:
--   Finite CP decompositions and commutant POVMs
-- statement:
--   Let $\mathcal A$ be a concrete unital complex C*-algebra, and let $T:\mathcal A\to B(H)$ be normal and CP. Fix a minimal dilation $T(a)=V^*\pi(a)V$ on a complex separable Hilbert space $K$. For a finite index set $I$ and normal CP maps $T_i$ with $T=\sum_{i\in I}T_i$, there is a unique family $(F_i)_{i\in I}$ such that
--
--   $$F_i\in\pi(\mathcal A)',\quad F_i\ge0,\quad\sum_{i\in I}F_i=I_K,\qquad T_i(a)=V^*\pi(a)F_iV.$$
--
--   This identifies finite CP decompositions with commutant POVMs. An empty index set is allowed only when $T=0$, when minimality forces $K=0$.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 8, Theorem 3.3: finite CP decompositions and commutant POVMs

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

/-- Theorem 3.3, PDF p.8: every finite CP decomposition gives a unique commutant POVM.
The empty index type forces T=0; minimality then forces a zero dilation space. -/
theorem finite_cp_decomposition {A : Type*} [CStarAlgebra A]
    (G H K : SeparableHilbertSpace) (rho : A →⋆ₐ[ℂ] HilbertEndomorphism G) (h_rho : Function.Injective rho)
    (T : A →ₗ[ℂ] HilbertEndomorphism H) (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hT : IsNormalCP rho T) (h_dilation : ∀ a, T a = compress V (pi a))
    (h_minimal : IsMinimal pi V) (I : Type*) [Fintype I]
    (Ti : I → A →ₗ[ℂ] HilbertEndomorphism H) (hTi : ∀ i, IsNormalCP rho (Ti i))
    (h_sum : T = ∑ i, Ti i) :
    ∃! F : I → HilbertEndomorphism K,
      (∀ i, (F i).IsPositive ∧ CommutesWithRepresentation pi (F i)) ∧
      (∑ i, F i) = ContinuousLinearMap.id ℂ K ∧
      ∀ i a, Ti i a = compress V ((pi a).comp (F i)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
