-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_augmentedConstraintDependence
-- name    : QAlgorithms.Papers.Independent.Next46.P27.augmentedConstraintDependence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:29:11.348984+00:00
-- url     : https://prove2.me/theorems/bfae0017-a71a-4eb8-8d05-7e4fde286844
-- title:
--   Dependence of the augmented constraint differentials
-- statement:
--   Let $E$ be a finite-dimensional real normed vector space, let $f,g_1,\ldots,g_m:E\to\mathbb R$ be differentiable at a point $x$ satisfying $g_j(x)=0$, and let $\lambda_1,\ldots,\lambda_m\in\mathbb R$. If the first-stage stationarity relation is
--
--   $$df(x)=\sum_{j=1}^m\lambda_j\,dg_j(x),$$
--
--   then the augmented family $df(x),dg_1(x),\ldots,dg_m(x)$ is linearly dependent. These differentials are the cotangent version of the gradients in Eqs.(15)–(16), with $f$ the first entropy objective and the $g_j$ its constraints.
--
--   The result explains failure of the constraint-independence condition for the second minimization. It asserts neither existence of competing minima nor sufficiency of stationarity.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 4, Section VII, Eqs.(15)–(16): augmented constraint dependence

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF pp.4–5, Eqs.(15)–(16): the first stationarity relation makes the
augmented family of constraint differentials linearly dependent. Differentials
are the cotangent version of the displayed Euclidean gradients. -/
theorem augmentedConstraintDependence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (m : ℕ)
    (f : E → ℝ) (g : Fin m → E → ℝ) (x : E) (lambda : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : ∀ j, DifferentiableAt ℝ (g j) x)
    (hfeasible : ∀ j, g j x = 0)
    (hstation : fderiv ℝ f x = ∑ j, lambda j • fderiv ℝ (g j) x) :
    ¬LinearIndependent ℝ (fun i : Unit ⊕ Fin m =>
      Sum.elim (fun _ : Unit => fderiv ℝ f x) (fun j => fderiv ℝ (g j) x) i) := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
