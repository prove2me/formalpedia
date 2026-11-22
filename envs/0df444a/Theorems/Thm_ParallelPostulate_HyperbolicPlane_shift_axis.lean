-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_axis
-- name    : ParallelPostulate.HyperbolicPlane.shift_axis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:00.357801+00:00
-- url     : https://prove2.me/theorems/9d13e6ac-c698-4eaa-8512-edad327dd20a
-- title:
--   Hyperbolic Plane: shift axis
-- statement:
--   On the first axis the motion is the step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L999-L1001
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L999-L1001

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

theorem ParallelPostulate.HyperbolicPlane.shift_axis (κ a w t : K) : shift κ a w (t, 0) = (step κ t a, 0) := by sorry
