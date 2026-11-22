-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_kleinInner
-- name    : ParallelPostulate.HyperbolicPlane.rot_kleinInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:19.66444+00:00
-- url     : https://prove2.me/theorems/7f77ba20-b8a7-4bd7-8257-662ca26928ca
-- title:
--   Hyperbolic Plane: rot klein Inner
-- statement:
--   **Turning keeps the inner product at a pair.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1597-L1601
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1597-L1601

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

theorem ParallelPostulate.HyperbolicPlane.rot_kleinInner {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P A B : K × K) :
    kleinInner κ (rot c s P) (rot c s A) (rot c s B) = kleinInner κ P A B := by sorry
