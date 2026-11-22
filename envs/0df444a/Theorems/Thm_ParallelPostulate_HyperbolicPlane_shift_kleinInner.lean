-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_kleinInner
-- name    : ParallelPostulate.HyperbolicPlane.shift_kleinInner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:21.282693+00:00
-- url     : https://prove2.me/theorems/8fc78fce-1108-43e4-96ec-743ca21d0932
-- title:
--   Hyperbolic Plane: shift klein Inner
-- statement:
--   **The motion along the first axis keeps the inner product at a pair**, up to a factor. The
--   factor is the same for every direction from the pair once each direction is divided by its
--   own denominator, and so the motion keeps angles: see `shift_kleinAngle`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1583-L1594
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1583-L1594

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

theorem ParallelPostulate.HyperbolicPlane.shift_kleinInner {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) {P A B : K × K}
    (hP : 1 - κ * a * P.1 ≠ 0) (hA : 1 - κ * a * A.1 ≠ 0) (hB : 1 - κ * a * B.1 ≠ 0) :
    kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w B)
      = w ^ 4 * kleinInner κ P A B
          / ((1 - κ * a * P.1) ^ 2 * (1 - κ * a * A.1) * (1 - κ * a * B.1)) := by sorry
