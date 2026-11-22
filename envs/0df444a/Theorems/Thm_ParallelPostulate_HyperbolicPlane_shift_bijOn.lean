-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_bijOn
-- name    : ParallelPostulate.HyperbolicPlane.shift_bijOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:19.58074+00:00
-- url     : https://prove2.me/theorems/565fc1d3-4614-475f-ad66-7b3639d29e75
-- title:
--   Hyperbolic Plane: shift bij On
-- statement:
--   **The motion takes the plane onto itself, and different points to different points.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1328-L1340
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1328-L1340

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

theorem ParallelPostulate.HyperbolicPlane.shift_bijOn {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) :
    Set.BijOn (shift κ a w) (plane κ) (plane κ) := by sorry
