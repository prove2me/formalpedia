-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_div_cube
-- name    : ParallelPostulate.HyperbolicPlane.hasDerivAt_div_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:50.427471+00:00
-- url     : https://prove2.me/theorems/5a049329-d580-4bea-aa72-a19892caaede
-- title:
--   Hyperbolic Plane: has Deriv At div cube
-- statement:
--   The derivative of a quotient by a cube.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2141-L2147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2141-L2147

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

theorem ParallelPostulate.HyperbolicPlane.hasDerivAt_div_cube {f b : ℝ → ℝ} {f' b' t : ℝ} (hf : HasDerivAt f f' t)
    (hb : HasDerivAt b b' t) (h : b t ≠ 0) :
    HasDerivAt (fun s => f s / b s ^ 3) ((f' * b t - 3 * f t * b') / b t ^ 4) t := by sorry
