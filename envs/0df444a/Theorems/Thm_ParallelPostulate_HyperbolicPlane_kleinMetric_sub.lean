-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinMetric_sub
-- name    : ParallelPostulate.HyperbolicPlane.kleinMetric_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:10.77152+00:00
-- url     : https://prove2.me/theorems/47dd6b16-741a-4f53-bee5-4b98314f193e
-- title:
--   Hyperbolic Plane: klein Metric sub
-- statement:
--   On the directions from `P` to `A` and from `P` to `B`, it is the inner product at `P`,
--   divided by the square of the bound at `P`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1852-L1856
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1852-L1856

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

theorem ParallelPostulate.HyperbolicPlane.kleinMetric_sub (κ : K) (P A B : K × K) :
    kleinMetric κ P (A - P) (B - P)
      = kleinInner κ P A B / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 := by sorry
