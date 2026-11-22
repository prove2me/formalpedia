-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_cross
-- name    : ParallelPostulate.HyperbolicPlane.rot_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:11.914499+00:00
-- url     : https://prove2.me/theorems/267d5075-b922-4735-9f0d-a1e94ed4f63b
-- title:
--   Hyperbolic Plane: rot cross
-- statement:
--   **Turning keeps left and right**: it keeps the cross product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1194-L1199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1194-L1199

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

theorem ParallelPostulate.HyperbolicPlane.rot_cross {c s : K} (h : c ^ 2 + s ^ 2 = 1) (A B C : K × K) :
    cross ((rot c s B).1 - (rot c s A).1, (rot c s B).2 - (rot c s A).2)
        ((rot c s C).1 - (rot c s A).1, (rot c s C).2 - (rot c s A).2)
      = cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) := by sorry
