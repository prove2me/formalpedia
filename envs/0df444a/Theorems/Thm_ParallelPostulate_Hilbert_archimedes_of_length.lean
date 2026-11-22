-- Prove2me | Theorems.Thm_ParallelPostulate_Hilbert_archimedes_of_length
-- name    : ParallelPostulate.Hilbert.archimedes_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:55.194757+00:00
-- url     : https://prove2.me/theorems/ae5d3a71-fa87-4187-ab97-9524593e2086
-- title:
--   Hilbert: archimedes of length
-- statement:
--   **Archimedes' axiom, from a length.** Suppose a length of segments of the plane is 0 for
--   a point and positive for two different points, adds along a segment, is equal for two segments
--   exactly when `apart` is, and takes every positive value on every ray. Then the plane meets
--   Archimedes' axiom.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4294-L4394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L4294-L4394

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

theorem ParallelPostulate.Hilbert.archimedes_of_length {κ : ℝ} (hκ : κ ≤ 0) (len : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hcong : ∀ {P Q R S : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → R ∈ plane κ → S ∈ plane κ →
      (apart κ P Q = apart κ R S ↔ len P Q = len R S))
    (hadd : ∀ {A B C : ℝ × ℝ}, A ∈ plane κ → C ∈ plane κ → Between A B C →
      len A C = len A B + len B C)
    (hpos : ∀ {P Q : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → P ≠ Q → 0 < len P Q)
    (hzero : ∀ {P : ℝ × ℝ}, P ∈ plane κ → len P P = 0)
    (hexist : ∀ {O D : ℝ × ℝ}, O ∈ plane κ → O ≠ D → ∀ d, 0 < d →
      ∃ t, 0 < t ∧ (Dim.mk O D).pt t ∈ plane κ ∧ len O ((Dim.mk O D).pt t) = d) :
    (model κ hκ).Archimedes := by sorry
