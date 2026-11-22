-- Prove2me | Theorems.Thm_ParallelPostulate_Hilbert_cut_point
-- name    : ParallelPostulate.Hilbert.cut_point
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:01.189437+00:00
-- url     : https://prove2.me/theorems/7a4b0131-7c3c-4fa0-b314-c7186f8c9575
-- title:
--   Hilbert: cut point
-- statement:
--   **A cut of an interval of real numbers has one cut point.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4194-L4225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4194-L4225

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

theorem ParallelPostulate.Hilbert.cut_point {I S T : Set ℝ} (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hST : ∀ t, t ∈ I ↔ t ∈ S ∨ t ∈ T) (hdisj : ∀ t ∈ S, t ∉ T) (hSne : S.Nonempty)
    (hTne : T.Nonempty) (hS : ∀ x ∈ S, ∀ y ∈ T, ∀ z ∈ T, ¬ StrictBetween y x z)
    (hT : ∀ x ∈ T, ∀ y ∈ S, ∀ z ∈ S, ¬ StrictBetween y x z) :
    ∃! c, c ∈ I ∧ ∀ a ∈ S, ∀ b ∈ T, a ≠ c → b ≠ c → StrictBetween a c b := by sorry
