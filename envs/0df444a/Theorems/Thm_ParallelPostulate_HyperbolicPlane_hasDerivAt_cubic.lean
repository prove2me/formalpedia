-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_cubic
-- name    : ParallelPostulate.HyperbolicPlane.hasDerivAt_cubic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:30.252552+00:00
-- url     : https://prove2.me/theorems/559fac9d-acf8-4c0a-8586-5e8675b0d615
-- title:
--   Hyperbolic Plane: has Deriv At cubic
-- statement:
--   The derivative of a polynomial of degree at most 3.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2117-L2129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2117-L2129

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Filter Topology

theorem ParallelPostulate.HyperbolicPlane.hasDerivAt_cubic (c0 c1 c2 c3 : ℝ) {f : ℝ → ℝ}
    (hf : ∀ s, f s = c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3) (t : ℝ) :
    HasDerivAt f (c1 + 2 * c2 * t + 3 * c3 * t ^ 2) t := by sorry
