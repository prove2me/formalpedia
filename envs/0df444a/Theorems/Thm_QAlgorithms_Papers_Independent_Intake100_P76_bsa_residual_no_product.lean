-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_bsa_residual_no_product
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.bsa_residual_no_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:25:30.419517+00:00
-- url     : https://prove2.me/theorems/074a4dd0-0c59-4f6f-83ca-9e70256f6a6b
-- title:
--   No nonzero product vector lies in an optimal residual range
-- statement:
--   Let $H_A$ and $H_B$ be finite-dimensional nonzero complex Hilbert spaces, with $H_A$ the first tensor factor, and let $\rho$ be a positive semidefinite operator of trace one on $H_A\otimes H_B$. A best separable approximation is an unnormalized separable positive operator $S$ such that $\rho-S\succeq0$ and $\operatorname{Tr}S$ is maximal among all such operators. For any such optimizer $S$, if $R=\rho-S\neq0$, then for arbitrary local vectors $e\in H_A$ and $f\in H_B$,
--
--   $$e\otimes f\neq0\quad\Longrightarrow\quad e\otimes f\notin\operatorname{range}R.$$
--
--   The residual can be unnormalized. The statement characterizes the absence of further removable product projectors at an unrestricted optimum.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 3, Unnumbered after Theorem 2: globally optimal residual contains no product vector

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.3, after Theorem 2: a nonzero unrestricted optimal residual has no
nonzero product vector in its range. The residual need not have trace one. -/
theorem bsa_residual_no_product [Nonempty A] [Nonempty B]
    (rho S : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (hS : IsBSA rho S) (hR : rho - S ≠ 0) :
    ∀ (e : EuclideanSpace ℂ A) (f : EuclideanSpace ℂ B),
      tensorVec e f ≠ 0 →
        tensorVec e f ∉ LinearMap.range (Matrix.toEuclideanLin (rho - S)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
