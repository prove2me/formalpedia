-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_side_iff_right
-- name    : ParallelPostulate.ThreeDimensions.meet_on_side_iff_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:20.899182+00:00
-- url     : https://prove2.me/theorems/6e4e0dc6-23c4-419f-a340-aed835e63654
-- title:
--   Three Dimensions: meet on side iff right
-- statement:
--   **Exactly when, on the other side.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L475-L489
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L475-L489

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

theorem ParallelPostulate.ThreeDimensions.meet_on_side_iff_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ cross F.b.dir F.c.dir < 0 := by sorry
