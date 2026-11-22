-- Prove2me | Theorems.Thm_ParallelPostulate_Hilbert_model_archimedes
-- name    : ParallelPostulate.Hilbert.model_archimedes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:54.972177+00:00
-- url     : https://prove2.me/theorems/97e886b1-3f1c-4e62-aa1c-a80a7ddb869e
-- title:
--   Hilbert: model archimedes
-- statement:
--   **Archimedes' axiom holds in the plane of a bound that is not positive.** Under a negative
--   bound the length is Klein's distance; under the bound 0 it is the square root of `apart`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4398-L4449
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4398-L4449

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
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane

theorem ParallelPostulate.Hilbert.model_archimedes (κ : ℝ) (hκ : κ ≤ 0) : (model κ hκ).Archimedes := by sorry
