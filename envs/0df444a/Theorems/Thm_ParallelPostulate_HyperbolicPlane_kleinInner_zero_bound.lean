-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinInner_zero_bound
-- name    : ParallelPostulate.HyperbolicPlane.kleinInner_zero_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:18.999871+00:00
-- url     : https://prove2.me/theorems/f3f3c78a-714e-4ef2-bcc7-a2f5d694d609
-- title:
--   Hyperbolic Plane: klein Inner zero bound
-- statement:
--   With the bound 0 it is the inner product of Euclid.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1523-L1525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1523-L1525

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

theorem ParallelPostulate.HyperbolicPlane.kleinInner_zero_bound (P A B : K × K) :
    kleinInner 0 P A B = (A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2) := by sorry
