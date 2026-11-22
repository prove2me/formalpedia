-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_pasch
-- name    : ParallelPostulate.HyperbolicPlane.pasch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:36.500415+00:00
-- url     : https://prove2.me/theorems/8053b827-70c4-4070-b273-83f6ace0e9c1
-- title:
--   Hyperbolic Plane: pasch
-- statement:
--   **Pasch's axiom.** Let `A`, `B` and `C` be points of the plane, and let a dimension pass
--   through none of them. If it has a pair between `A` and `B`, it has a point of the plane between
--   `A` and `C`, or between `B` and `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1141-L1173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1141-L1173

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.pasch (κ : K) {A B C : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ)
    (hC : C ∈ plane κ) (M : Dim K) (hM : M.zero ≠ M.one) (hAM : A ∉ M.points)
    (hBM : B ∉ M.points) (hCM : C ∉ M.points) {X : K × K} (hX : X ∈ M.points)
    (hAXB : Between A X B) :
    ∃ Y : K × K, Y ∈ M.points ∧ Y ∈ plane κ ∧ (Between A Y C ∨ Between B Y C) := by sorry
