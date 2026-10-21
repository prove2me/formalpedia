-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_positive_kernel_kraus
-- name    : QAlgorithms.Papers.Independent.Support21.P17.positive_kernel_kraus
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:42:48.779352+00:00
-- url     : https://prove2.me/theorems/c04abb07-8e1d-492c-b325-c722827f8df9
-- title:
--   Positive-kernel Kraus form
-- statement:
--   Let $T:B(H)\to B(K)$ be normal and CP on complex separable Hilbert spaces. Fix its canonical dilation $V:K\to H\otimes E$, a complete orthonormal environment basis $(e_x)_{x\in X}$ with at most countable $X$, and the induced Kraus family $(W_x)$ defined by $V\eta=\sum_x W_x\eta\otimes e_x$. For every normal CP map $S:B(H)\to B(K)$,
--
--   $$S\le T\iff\exists C:X\times X\to\mathbb C,\quad 0\le C\le I,\qquad S(A)=\sum_{x,y\in X}C(x,y)W_x^*AW_y.$$
--
--   Here $I(x,y)=\delta_{xy}$, and kernel positivity means $\sum_{i,j}\overline{c_i}c_jC(x_i,x_j)\ge0$ for every finite choice of points and complex coefficients. The double series converges strongly through independent finite rectangular truncations. This gives coordinates for the same order interval without asserting absolute operator-norm summability.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 9, Theorem 3.4: positive-kernel Kraus form

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

/-- Theorem 3.4, PDF pp.9–10: fixed canonical-induced Kraus family, positive kernel
order, and strong rectangular convergence of the double series. -/
theorem positive_kernel_kraus (H K E : SeparableHilbertSpace)
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hT : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T) (hV : IsCanonical T V)
    (X : Type) [Countable X] (e : HilbertBasis X ℂ E)
    (W : X → K →L[ℂ] H) (hW : IsInducedKraus e V W)
    (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (hS : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) S) :
    CompletelyDominated S T ↔ ∃ C : X → X → ℂ, KernelContraction C ∧ HasKernelExpansion W C S := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
