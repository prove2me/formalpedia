-- Prove2me | Theorems.Thm_SmoothLinearAlgebra_compact_supported_linear_solution
-- name    : SmoothLinearAlgebra.compact_supported_linear_solution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:13:40.198599+00:00
-- url     : https://prove2.me/theorems/db71746c-a663-42b8-8217-2f8fc9b9c797
-- title:
--   Smooth compactly supported solution of a parameterized linear system
-- statement:
--   Let P be a finite-dimensional real normed space, V a real Banach space, W a real normed space, and C a compact subset of P. Suppose A:P→L(V,W) and b:P→W are smooth and A(p) is a continuous linear isomorphism for every p in C. There exist smooth functions u:P→V and χ:P→ℝ such that u has compact support, χ=1 on C, and
--
--   $$ A(p)u(p)=\chi(p)b(p) \qquad(p\in P). $$
--
--   In particular u solves the original system on C. The construction extends a smooth inverse solution near a compact parameter set to a global smooth function while retaining all homogeneous linear constraints.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed p. 15, equations (2.1)-(2.2). Independent auxiliary formulation for smooth Moser selection; the linear-algebra and cutoff arguments are supplied in the accompanying proof. Smooth operator inversion and cutoff foundations use Mathlib ContDiff.Operations and BumpFunction.FiniteDimension at commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Tactic.Linarith

open Set Function
open scoped ContDiff Topology

set_option autoImplicit false

theorem SmoothLinearAlgebra.compact_supported_linear_solution
    {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : P → V →L[ℝ] W) (b : P → W)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (C : Set P) (hC : IsCompact C) (hi : ∀ p ∈ C, (A p).IsInvertible) :
    ∃ u : P → V, ∃ χ : P → ℝ,
      ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport u ∧
      (∀ p ∈ C, χ p = 1) ∧ (∀ p, A p (u p) = χ p • b p) := by sorry
