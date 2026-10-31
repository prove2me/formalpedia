-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_maximal_single_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.maximal_single_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:23:50.527803+00:00
-- url     : https://prove2.me/theorems/013097f3-b718-45aa-8314-c5b9653133c7
-- title:
--   Maximal subtraction of one rank-one projector
-- statement:
--   Let $A\succeq0$ act on a finite-dimensional nonzero complex Hilbert space, without a trace normalization, and let $\psi$ be a unit vector. Write $P=|\psi\rangle\langle\psi|$ and let $A^+$ invert the positive eigenvalues of $A$ and vanish on its kernel. A real coefficient $\Lambda$ is maximal when it is nonnegative, $A-\Lambda P\succeq0$, and $A-(\Lambda+\epsilon)P$ fails to be positive semidefinite for every $\epsilon>0$. Then
--
--   $$\Lambda\text{ is maximal}\iff\begin{cases}\Lambda=0,&\psi\notin\operatorname{range}A,\\0<\Lambda=\langle\psi,A^+\psi\rangle^{-1},&\psi\in\operatorname{range}A.\end{cases}$$
--
--   This gives the exact amount of a single pure projector that can be removed.
--
--   **Formalization Note** The inverse expectation is real on this domain. Definition 1 is read according to its proof: strictly positive increases must fail positive semidefiniteness.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 2, Lemma 1, Eq. (6): maximal single-projector subtraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.2, Lemma 1, Eq. (6). The inverse is on the support. Definition 1's
printed strictness and positivity wording are corrected to the meaning used
in its proof: every strictly larger coefficient fails PSD. -/
theorem maximal_single_iff [Nonempty I] (rho : Matrix I I ℂ)
    (hrho : rho.PosSemidef) (psi : EuclideanSpace ℂ I) (hpsi : IsState psi)
    (lambda : ℝ) :
    MaximalSingle rho psi lambda ↔
      (psi ∉ LinearMap.range (Matrix.toEuclideanLin rho) → lambda = 0) ∧
      (psi ∈ LinearMap.range (Matrix.toEuclideanLin rho) →
        0 < lambda ∧ lambda =
          ((inner ℂ psi (act (QAlgorithms.Papers.Independent.Dependency50.P26.pseudoInverse rho) psi)).re)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
