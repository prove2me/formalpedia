-- Prove2me | Theorems.Thm_RadialGeometry_radial_derivative_tangent_injective
-- name    : RadialGeometry.radial_derivative_tangent_injective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T19:18:44.549375+00:00
-- url     : https://prove2.me/theorems/02e4bcdb-8e70-4259-b9d7-0da62497e70f
-- title:
--   Injectivity of radial-rescaling derivatives on orthogonal tangents
-- statement:
--   In any real inner product space, let a be a real-valued function differentiable at u with a(u) nonzero. For any vector v orthogonal to u, if the derivative of the radial rescaling x ↦ a(x)x at u annihilates v, then v=0. Thus this derivative has trivial kernel on the orthogonal tangent space. Neither positivity of a(u), unit length of u, finite dimension nor completeness is required.
-- source:
--   Original generalization of radial_derivative_tangent_injective in Solutions/Sol_BirkhoffGlobalSection_convex_model_complete_sphere_reeb_flow.lean:29. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/Calculus/FDeriv/Mul.lean and Analysis/InnerProductSpace/Basic.lean. https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis. No separate article theorem or novelty claim.

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

theorem RadialGeometry.radial_derivative_tangent_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : E → ℝ) (u v : E) (ha : DifferentiableAt ℝ a u)
    (hane : a u ≠ 0) (hv : inner ℝ u v = 0)
    (hz : fderiv ℝ (fun x => a x • x) u v = 0) : v = 0 := by sorry
