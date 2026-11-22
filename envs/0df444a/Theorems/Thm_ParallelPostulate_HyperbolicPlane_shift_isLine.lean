-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_isLine
-- name    : ParallelPostulate.HyperbolicPlane.shift_isLine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:25.090585+00:00
-- url     : https://prove2.me/theorems/4bb0074c-6ebb-42bb-b2af-ce448d0164e5
-- title:
--   Hyperbolic Plane: shift is Line
-- statement:
--   **The motion takes lines of the plane to lines of the plane.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1390-L1437
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1390-L1437

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
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.shift_isLine {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {S : Set (K × K)} (hS : IsLine (plane κ) S) :
    IsLine (plane κ) (shift κ a w '' S) := by sorry
