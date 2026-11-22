-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_keeps_left
-- name    : ParallelPostulate.HyperbolicPlane.shift_keeps_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:21.4096+00:00
-- url     : https://prove2.me/theorems/38285bb6-06c5-44b2-ac09-dcced3ff2626
-- title:
--   Hyperbolic Plane: shift keeps left
-- statement:
--   **With `w` positive the motion keeps left and right.** For three points of the plane, the
--   cross product is positive, negative or zero after the motion as it was before.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1344-L1378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1344-L1378

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

theorem ParallelPostulate.HyperbolicPlane.shift_keeps_left {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : 0 < w)
    {A B C : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ) (hC : C ∈ plane κ) :
    (0 < cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) ↔
      0 < cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) < 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) < 0) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) = 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) = 0) := by sorry
