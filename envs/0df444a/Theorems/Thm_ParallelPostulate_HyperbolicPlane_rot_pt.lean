-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_pt
-- name    : ParallelPostulate.HyperbolicPlane.rot_pt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:11.129042+00:00
-- url     : https://prove2.me/theorems/7ee4111b-4bdf-48f8-a9cb-8fe25adf744b
-- title:
--   Hyperbolic Plane: rot pt
-- statement:
--   Turning takes the numbers of a dimension to the numbers of a dimension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1202-L1208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1202-L1208

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

theorem ParallelPostulate.HyperbolicPlane.rot_pt (c s : K) (M : Dim K) (t : K) :
    rot c s (M.pt t) = (Dim.mk (rot c s M.zero) (rot c s M.one)).pt t := by sorry
