-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_side_iff
-- name    : ParallelPostulate.ThreeDimensions.meet_on_side_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:51.246508+00:00
-- url     : https://prove2.me/theorems/d7650ee4-afaa-490f-8b5a-a6b4571a8195
-- title:
--   Three Dimensions: meet on side iff
-- statement:
--   **Exactly when.** The lines `b` and `c` meet on the side of `b1` and `c1` exactly when `c`
--   is a turn to the left of `b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L433-L447
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L433-L447

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

theorem ParallelPostulate.ThreeDimensions.meet_on_side_iff (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ 0 < cross F.b.dir F.c.dir := by sorry
