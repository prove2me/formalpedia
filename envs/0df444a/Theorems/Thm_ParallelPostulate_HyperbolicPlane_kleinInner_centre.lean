-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinInner_centre
-- name    : ParallelPostulate.HyperbolicPlane.kleinInner_centre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:17.644582+00:00
-- url     : https://prove2.me/theorems/9bae4ab4-8bad-4ef0-a5ab-35e3a39616cd
-- title:
--   Hyperbolic Plane: klein Inner centre
-- statement:
--   At `(0, 0)` it is the inner product of Euclid, under any bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1528-L1530
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1528-L1530

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

theorem ParallelPostulate.HyperbolicPlane.kleinInner_centre (κ : K) (A B : K × K) :
    kleinInner κ (0, 0) A B = A.1 * B.1 + A.2 * B.2 := by sorry
