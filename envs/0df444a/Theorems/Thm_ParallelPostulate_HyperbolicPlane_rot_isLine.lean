-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_isLine
-- name    : ParallelPostulate.HyperbolicPlane.rot_isLine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:27.516039+00:00
-- url     : https://prove2.me/theorems/08d19601-4a48-4a88-825b-16359170aca7
-- title:
--   Hyperbolic Plane: rot is Line
-- statement:
--   **Turning takes lines of the plane to lines of the plane.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1463-L1477
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1463-L1477

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

theorem ParallelPostulate.HyperbolicPlane.rot_isLine {c s : K} (h : c ^ 2 + s ^ 2 = 1) {κ : K} {S : Set (K × K)}
    (hS : IsLine (plane κ) S) : IsLine (plane κ) (rot c s '' S) := by sorry
