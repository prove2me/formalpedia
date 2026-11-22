-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_cross
-- name    : ParallelPostulate.HyperbolicPlane.shift_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:01.619187+00:00
-- url     : https://prove2.me/theorems/49b8ebef-849e-4427-b850-1af2efd2b27e
-- title:
--   Hyperbolic Plane: shift cross
-- statement:
--   **A motion keeps three pairs of a dimension on a dimension.** If `w (1 + κ a²)` is not
--   zero, it keeps three pairs that are not on one dimension off it as well.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1064-L1076
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1064-L1076

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

theorem ParallelPostulate.HyperbolicPlane.shift_cross (κ a w : K) {A B C : K × K} (hA : 1 - κ * a * A.1 ≠ 0)
    (hB : 1 - κ * a * B.1 ≠ 0) (hC : 1 - κ * a * C.1 ≠ 0) :
    cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2)
      = w * (1 + κ * a ^ 2) * cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)
          / ((1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1)) := by sorry
