-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_fifth_postulate_right
-- name    : ParallelPostulate.ThreeDimensions.fifth_postulate_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:24.937235+00:00
-- url     : https://prove2.me/theorems/db6af393-4dfd-4c0d-9095-a9f45f0a0ec6
-- title:
--   Three Dimensions: fifth postulate right
-- statement:
--   **The postulate on the other side of `a`.** If `b1` and `c1` lie on the right of `a`, and
--   `c` is a turn to the right of `b`, the lines meet on the right of `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L451-L460
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L451-L460

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
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ParallelPostulate.ThreeDimensions.fifth_postulate_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hsum : cross F.b.dir F.c.dir < 0) :
    ∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by sorry
