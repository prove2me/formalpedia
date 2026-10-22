-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_markov_projection_characterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.markov_projection_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:46:31.321867+00:00
-- url     : https://prove2.me/theorems/2723f590-6d7e-4d4f-8bee-ee43cbb56ad7
-- title:
--   Markov quasifree triplets characterized by a separating projection
-- statement:
--   Let $H=H_1\oplus H_2\oplus H_3$ be a finite-dimensional orthogonal decomposition and let $A\ge0$ be a quasifree one-particle covariance. Put $g(x)=(x+1)\log(x+1)-x\log x$, with $0\log0=0$, and $\mathcal S(T)=\operatorname{Tr}g(T)$. Then
--
--   $$\mathcal S(A)-\mathcal S(A_{23,23})=\mathcal S(A_{12,12})-\mathcal S(A_{22})$$
--
--   if and only if there exists an orthogonal projection $P$ on $H$ satisfying
--
--   $$P^*=P,\qquad P^2=P,\qquad P|_{H_1}=I,\qquad P|_{H_3}=0,\qquad PA=AP.$$
--
--   The left side is precisely the full bosonic quasifree Markov entropy condition from (36), using Theorem 1.3 for each actual marginal. The characterization permits kernels and zero-dimensional summands. It describes block diagonality after splitting the middle time space; it does not assert block diagonality in the original three time factors.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 17, Theorem 2.3 (paper headline)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- Theorem 2.3, PDF pp.17–20: both directions, for all positive-semidefinite A.
IsMarkov is (36) evaluated by the explicit entropy formula, including kernels. -/
theorem markov_projection_characterization (A : Mat (I ⊕ (J ⊕ K))) (hA : A.PosSemidef) :
    IsMarkov A ↔ ∃ P : Mat (I ⊕ (J ⊕ K)), SeparatingProjection A P := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
