-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_centre
-- name    : ParallelPostulate.HyperbolicPlane.shift_centre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:57.631623+00:00
-- url     : https://prove2.me/theorems/39b034f8-7aa2-4dfa-85ba-48c801f3dcbd
-- title:
--   Hyperbolic Plane: shift centre
-- statement:
--   The Hyperbolic Plane construction uses the shift centre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L995-L996
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L995-L996

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
variable {K : Type*} [Field K]

theorem ParallelPostulate.HyperbolicPlane.shift_centre (κ a w : K) : shift κ a w (0, 0) = (a, 0) := by sorry
