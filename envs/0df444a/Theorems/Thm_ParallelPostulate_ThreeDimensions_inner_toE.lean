-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_inner_toE
-- name    : ParallelPostulate.ThreeDimensions.inner_toE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:47.577877+00:00
-- url     : https://prove2.me/theorems/289ff8ce-baf4-4f3b-9637-beb380fc2c4f
-- title:
--   Three Dimensions: inner to E
-- statement:
--   The Three Dimensions construction uses the inner to E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L590-L592
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L590-L592

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
open Real InnerProductGeometry

theorem ParallelPostulate.ThreeDimensions.inner_toE (p q : ℝ × ℝ) : inner ℝ (toE p) (toE q) = p.1 * q.1 + p.2 * q.2 := by sorry
