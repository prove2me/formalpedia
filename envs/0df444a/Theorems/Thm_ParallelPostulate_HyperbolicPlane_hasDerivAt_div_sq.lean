-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_hasDerivAt_div_sq
-- name    : ParallelPostulate.HyperbolicPlane.hasDerivAt_div_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:47.951404+00:00
-- url     : https://prove2.me/theorems/936ba3e4-0d5e-4b6a-b17a-dad5159302d0
-- title:
--   Hyperbolic Plane: has Deriv At div sq
-- statement:
--   The derivative of a quotient by a square.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2132-L2138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2132-L2138

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

theorem ParallelPostulate.HyperbolicPlane.hasDerivAt_div_sq {f b : ℝ → ℝ} {f' b' t : ℝ} (hf : HasDerivAt f f' t)
    (hb : HasDerivAt b b' t) (h : b t ≠ 0) :
    HasDerivAt (fun s => f s / b s ^ 2) ((f' * b t - 2 * f t * b') / b t ^ 3) t := by sorry
