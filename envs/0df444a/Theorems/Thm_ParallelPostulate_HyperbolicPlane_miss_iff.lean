-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_miss_iff
-- name    : ParallelPostulate.HyperbolicPlane.miss_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:50.236118+00:00
-- url     : https://prove2.me/theorems/738cb4dd-77d6-4829-9d6e-8d03a5d8849f
-- title:
--   Hyperbolic Plane: miss iff
-- statement:
--   **When two lines of the plane do not meet.** Let `M` pass through a pair that is not a
--   pair of `L`. What `M` and `L` have in the plane has no point in common exactly when `M` has the
--   direction of `L`, or the two dimensions meet at a pair that is not a point of the plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L615-L639
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L615-L639

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
variable {K : Type*} [Field K]

theorem ParallelPostulate.HyperbolicPlane.miss_iff (Pl : Set (K × K)) (L M : Dim K) (hL : L.zero ≠ L.one) {P : K × K}
    (hP : P ∈ M.points) (hPL : P ∉ L.points) :
    (M.points ∩ Pl) ∩ (L.points ∩ Pl) = ∅ ↔
      cross L.dir M.dir = 0 ∨ ∃ Q, Q ∈ L.points ∧ Q ∈ M.points ∧ Q ∉ Pl := by sorry
