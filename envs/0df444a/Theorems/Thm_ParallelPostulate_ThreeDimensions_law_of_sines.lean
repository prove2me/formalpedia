-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_law_of_sines
-- name    : ParallelPostulate.ThreeDimensions.law_of_sines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:28.025002+00:00
-- url     : https://prove2.me/theorems/4ee5e587-7105-4eb6-ab4e-36adffd8310e
-- title:
--   Three Dimensions: law of sines
-- statement:
--   **Where they meet: the law of sines.** The point is at the number `sin γ / sin (β + γ)` of
--   `b`, and at the number `sin β / sin (β + γ)` of `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L557-L568
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L557-L568

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
open ParallelPostulate.ThreeDimensions
open Pairs
open Real

theorem ParallelPostulate.ThreeDimensions.law_of_sines (β γ : ℝ) (h : sin (β + γ) ≠ 0) :
    (angleFigure β γ).b.pt (sin γ / sin (β + γ))
      = (angleFigure β γ).c.pt (sin β / sin (β + γ)) := by sorry
