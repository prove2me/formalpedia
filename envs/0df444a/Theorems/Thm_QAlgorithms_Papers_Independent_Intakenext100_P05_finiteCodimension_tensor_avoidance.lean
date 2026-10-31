-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P05_finiteCodimension_tensor_avoidance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P05.finiteCodimension_tensor_avoidance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T03:53:09.555865+00:00
-- url     : https://prove2.me/theorems/bf5dd6d4-d807-4537-8f47-95467e774d33
-- title:
--   Finite-codimension tensor avoidance
-- statement:
--   Let $H$ be an infinite-dimensional separable complex Hilbert space, let $n\geq 0$ be an integer, and let $W$ be a finite-dimensional complex linear subspace of $\mathbb C^n\otimes_{\mathbb C}H$. Then there is a closed complex linear subspace $V\subseteq H$ such that
--
--   $$
--   \dim_{\mathbb C}(H/V)<\infty,
--   \qquad (\mathbb C^n\otimes_{\mathbb C}V)\cap W=\{0\}.
--   $$
--
--   Here the tensor subspace is viewed inside $\mathbb C^n\otimes_{\mathbb C}H$ through the map induced by $V\hookrightarrow H$. Since the first factor is finite-dimensional, its algebraic tensor product gives the same vector space as the Hilbert tensor product. The statement supplies the linear avoidance step used in the torsion index construction.
--
--   **Formalization Note** Finite codimension is expressed by finite-dimensionality of the quotient $H/V$, without a numerical `finrank` test.
-- source:
--   Twisted K-theory and K-theory of bundle gerbes, arXiv:hep-th/0106194v2, PDF p. 10, Lemma 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P05

namespace QAlgorithms.Papers.Independent.Intakenext100.P05

open scoped TensorProduct

/-- Lemma 6.2 (PDF p. 10): a finite-dimensional subspace of C^n tensor H
is disjoint from C^n tensor V for some closed finite-codimension subspace V of H.
The standing Hilbert-space assumptions are from PDF pp. 5 and 21.
The tensor subspace is the range of the actual map induced by V's inclusion;
finite codimension means that H/V is finite-dimensional. The source proof's
interchanged V/W names are read using its coordinate-span orthogonal complement.
No positivity condition on n is imposed. -/
theorem finiteCodimension_tensor_avoidance
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (hInfinite : ¬ FiniteDimensional ℂ H)
    (n : ℕ) (W : Submodule ℂ ((Fin n → ℂ) ⊗[ℂ] H))
    [FiniteDimensional ℂ W] :
    ∃ V : Submodule ℂ H,
      IsClosed (V : Set H) ∧
      FiniteDimensional ℂ (H ⧸ V) ∧
      (TensorProduct.map
        (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) V.subtype).range ⊓ W = ⊥ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P05
