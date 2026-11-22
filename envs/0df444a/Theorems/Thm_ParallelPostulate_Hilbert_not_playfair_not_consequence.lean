-- Prove2me | Theorems.Thm_ParallelPostulate_Hilbert_not_playfair_not_consequence
-- name    : ParallelPostulate.Hilbert.not_playfair_not_consequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:16:48.357358+00:00
-- url     : https://prove2.me/theorems/38839010-ecac-496a-9ded-7f5ab6197e7c
-- title:
--   Hilbert: not playfair not consequence
-- statement:
--   Nor does its negation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4522-L4523
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4522-L4523

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

theorem ParallelPostulate.Hilbert.not_playfair_not_consequence : ¬ ∀ (P L : Type) (H : HilbertPlane P L), ¬ H.Playfair := by sorry
