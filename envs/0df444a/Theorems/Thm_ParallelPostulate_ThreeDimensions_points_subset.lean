-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_points_subset
-- name    : ParallelPostulate.ThreeDimensions.points_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:27.096481+00:00
-- url     : https://prove2.me/theorems/c63a5219-9e7a-4681-b891-f6a765316f3d
-- title:
--   Three Dimensions: points subset
-- statement:
--   If the direction of `M` is a multiple of the direction of `M'`, and they leave the same
--   point, every point of `M` is a point of `M'`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L322-L335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L322-L335

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
open ParallelPostulate.ThreeDimensions
open Pairs
variable {K : Type*} [Field K]

theorem ParallelPostulate.ThreeDimensions.points_subset (M M' : Dim K) (hP : M.zero = M'.zero) (k : K)
    (hk : M.dir = (k * M'.dir.1, k * M'.dir.2)) : M.points ⊆ M'.points := by sorry
