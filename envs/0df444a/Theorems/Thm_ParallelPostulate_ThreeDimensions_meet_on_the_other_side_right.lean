-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_the_other_side_right
-- name    : ParallelPostulate.ThreeDimensions.meet_on_the_other_side_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:20.453598+00:00
-- url     : https://prove2.me/theorems/a4e02bb2-0552-4c23-97c7-82ea1d77cc09
-- title:
--   Three Dimensions: meet on the other side right
-- statement:
--   **More than two right angles, on the right of `a`: the lines meet on the left of `a`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L463-L472
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L463-L472

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

theorem ParallelPostulate.ThreeDimensions.meet_on_the_other_side_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) := by sorry
