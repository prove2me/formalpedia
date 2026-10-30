-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_pure_reduction_symmetry
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.pure_reduction_symmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:35:13.339282+00:00
-- url     : https://prove2.me/theorems/8180a30b-c3ee-4341-82a0-c0cfdcef6957
-- title:
--   V A: pure-state gauge invariance is equivalent to dependence on algebra reduction
-- statement:
--   Let $\mathcal A$ be a unital adjoint-closed algebra on a nonzero finite-dimensional complex Hilbert space. Let $S$ be any $G_{\mathcal A}$-invariant family of pure density matrices, and let $g:S\to\mathbb R$. Then
--   $$g(U\rho U^*)=g(\rho)\ (U\in G_{\mathcal A},\rho\in S)
--   \iff [\rho|_{\mathcal A}=\sigma|_{\mathcal A}\Longrightarrow g(\rho)=g(\sigma)]\ (\rho,\sigma\in S).$$
--   The reduction $\rho|_{\mathcal A}$ is the functional $A\mapsto\operatorname{tr}(\rho A)$. Constancy on its fibers is equivalent to factoring through that reduction. No measurable factor or selector is asserted.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 21, V A: pure-state gauge invariance is equivalent to dependence on algebra reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.21-22: gauge invariance of a function on pure states is equivalent
to depending only on their algebra reduction. No measurable selector or
measurable factorization is asserted. -/
theorem pure_reduction_symmetry [Nonempty I] (A : StarSubalgebra ℂ (Mat I))
    (S : Set (Mat I)) (hS : ∀ rho ∈ S, IsDensityMatrix rho ∧ RankOne rho)
    (hstable : ∀ rho ∈ S, ∀ U ∈ unitaryCentralizer (A : Set (Mat I)), U * rho * Uᴴ ∈ S)
    (g : Mat I → ℝ) :
    (∀ rho ∈ S, ∀ U ∈ unitaryCentralizer (A : Set (Mat I)), g (U * rho * Uᴴ) = g rho) ↔
    (∀ rho ∈ S, ∀ sigma ∈ S, SameReduction (A : Set (Mat I)) rho sigma →
      g rho = g sigma) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
