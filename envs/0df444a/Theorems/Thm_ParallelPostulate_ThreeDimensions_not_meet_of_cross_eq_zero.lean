-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_not_meet_of_cross_eq_zero
-- name    : ParallelPostulate.ThreeDimensions.not_meet_of_cross_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:54.224355+00:00
-- url     : https://prove2.me/theorems/f7faa6ba-acef-4748-82c6-cd2a59036326
-- title:
--   Three Dimensions: not meet of cross eq zero
-- statement:
--   A dimension with the direction of `L`, through a point that is not on `L`, never meets
--   `L`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L285-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L285-L300

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

theorem ParallelPostulate.ThreeDimensions.not_meet_of_cross_eq_zero (L M : Dim K) (hL : L.zero ≠ L.one)
    (h : cross L.dir M.dir = 0) (hP : M.zero ∉ L.points) : ¬ Meet L M := by sorry
