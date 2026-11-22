-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinMetric_coords
-- name    : ParallelPostulate.HyperbolicPlane.kleinMetric_coords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:42.096609+00:00
-- url     : https://prove2.me/theorems/c0883dd8-b045-4e9f-b45d-6f1352de5eac
-- title:
--   Hyperbolic Plane: klein Metric coords
-- statement:
--   **Klein's metric is `E dx² + 2 F dx dy + G dy²`**, with `kleinE`, `kleinF` and `kleinG`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2110-L2114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2110-L2114

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

theorem ParallelPostulate.HyperbolicPlane.kleinMetric_coords (κ : ℝ) (p u v : ℝ × ℝ) :
    kleinMetric κ p u v
      = kleinE κ p * u.1 * v.1 + kleinF κ p * (u.1 * v.2 + u.2 * v.1) + kleinG κ p * u.2 * v.2 := by sorry
