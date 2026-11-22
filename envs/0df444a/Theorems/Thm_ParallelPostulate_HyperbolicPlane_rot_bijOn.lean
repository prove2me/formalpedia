-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_bijOn
-- name    : ParallelPostulate.HyperbolicPlane.rot_bijOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:27.248265+00:00
-- url     : https://prove2.me/theorems/2666cc41-d558-4365-803e-639ca233b62b
-- title:
--   Hyperbolic Plane: rot bij On
-- statement:
--   **Turning takes the plane onto itself, and different points to different points.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1447-L1459
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1447-L1459

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
omit [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.rot_bijOn {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) :
    Set.BijOn (rot c s) (plane κ) (plane κ) := by sorry
