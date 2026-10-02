-- Prove2me | Theorems.Thm_TegmarkDimensionality_coefficient_matrix_eigenvalue_signs
-- name    : TegmarkDimensionality.coefficient_matrix_eigenvalue_signs
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T05:05:52.132824+00:00
-- url     : https://prove2.me/theorems/1fb02dd3-b37d-4b2f-a37a-72242afc1c60
-- title:
--   $g^{-1}$ has the eigenvalue signs of the metric $g$
-- statement:
--   Let $g$ be a real symmetric square matrix with $\det g\neq0$. Then $g^{-1}$ has the same number of positive eigenvalues and the same number of negative eigenvalues as $g$, counted with multiplicity:
--   $$N_+(g^{-1})=N_+(g),\qquad N_-(g^{-1})=N_-(g).$$
--
--   For the covariant field equations the coefficient matrix is $A=g^{-1}$. The paper's remark that "$A$ has the same eigenvalues as the metric" is used for their signs only, which is what determines the PDE type.
--
--   **Formalization Note** The eigenvalues of $g^{-1}$ are the reciprocals of those of $g$, so the statement is about signs and not about equality of eigenvalues.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L73, second paragraph ('the matrix A will clearly have the same eigenvalues as the metric tensor')

import Mathlib
import Definitions.Def_tegmark_pde_classification

namespace TegmarkDimensionality

/-- The coefficient matrix `A = g⁻¹` of the covariant field equations has the same numbers
of positive and of negative eigenvalues as the (nondegenerate, symmetric) metric `g`. -/
theorem coefficient_matrix_eigenvalue_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Matrix ι ι ℝ) (hg : g.IsSymm) (hdet : g.det ≠ 0) :
    numPosEigenvalues g⁻¹ = numPosEigenvalues g ∧
      numNegEigenvalues g⁻¹ = numNegEigenvalues g := by sorry

end TegmarkDimensionality
