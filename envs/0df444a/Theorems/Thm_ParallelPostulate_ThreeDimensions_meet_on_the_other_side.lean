-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_the_other_side
-- name    : ParallelPostulate.ThreeDimensions.meet_on_the_other_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:56.178183+00:00
-- url     : https://prove2.me/theorems/c22b6ba1-e4a0-47f9-8a70-e37ed19fb6e4
-- title:
--   Three Dimensions: meet on the other side
-- statement:
--   **More than two right angles: the lines meet on the other side.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L420-L429
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L420-L429

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

theorem ParallelPostulate.ThreeDimensions.meet_on_the_other_side (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hsum : cross F.b.dir F.c.dir < 0) :
    ∃ t u : K, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by sorry
