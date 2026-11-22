-- Prove2me | Theorems.Thm_ParallelPostulate_Hilbert_cut_point_ordered
-- name    : ParallelPostulate.Hilbert.cut_point_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:57.810381+00:00
-- url     : https://prove2.me/theorems/290f1026-977b-40e0-bb2b-ac1ac075b404
-- title:
--   Hilbert: cut point ordered
-- statement:
--   A cut of an interval, with the first part below the second, has one cut point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4163-L4191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4163-L4191

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

theorem ParallelPostulate.Hilbert.cut_point_ordered {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hSne : S.Nonempty) (hTne : T.Nonempty)
    (hsep : ∀ s ∈ S, ∀ t ∈ T, s < t) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by sorry
