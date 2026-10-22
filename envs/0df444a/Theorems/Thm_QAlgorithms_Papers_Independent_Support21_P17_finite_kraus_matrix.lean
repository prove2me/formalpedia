-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_finite_kraus_matrix
-- name    : QAlgorithms.Papers.Independent.Support21.P17.finite_kraus_matrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:43:51.127192+00:00
-- url     : https://prove2.me/theorems/28078679-c1c9-4e68-98ab-f05414bcdece
-- title:
--   Finite coefficient-matrix Kraus form
-- statement:
--   Let $T:B(H)\to B(K)$ be normal CP, and fix a finite Kraus family $(W_x)_{x\in X}$ induced by a complete environment basis of a canonical minimal dilation. For any normal CP map $S$,
--
--   $$S\le T\iff\exists M\in M_X(\mathbb C),\quad M\ge0,\ I-M\ge0,\qquad S(A)=\sum_{x,y\in X}M_{xy}W_x^*AW_y\quad(A\in B(H)).$$
--
--   Both matrix inequalities are positive-semidefinite inequalities. This finite specialization provides usable matrix coordinates for domination of CP maps; it does not replace the canonical-family hypothesis by an arbitrary family.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 10, §3.2 remark 1: finite coefficient-matrix form

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

/-- Section 3.2 remark 1, PDF p.10: finite coefficient matrices are positive contractions
in matrix order, not entrywise order. The family is fixed before S. -/
theorem finite_kraus_matrix (H K E : SeparableHilbertSpace)
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hT : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T) (hV : IsCanonical T V)
    (X : Type) [Fintype X] (e : HilbertBasis X ℂ E)
    (W : X → K →L[ℂ] H) (hW : IsInducedKraus e V W)
    (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (hS : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) S) :
    CompletelyDominated S T ↔ ∃ M : Matrix X X ℂ, M.PosSemidef ∧ (1 - M).PosSemidef ∧
      ∀ A : HilbertEndomorphism H, S A = ∑ x, ∑ y,
        M x y • (ContinuousLinearMap.adjoint (W x)).comp (A.comp (W y)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
