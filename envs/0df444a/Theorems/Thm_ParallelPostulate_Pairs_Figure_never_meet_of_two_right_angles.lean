-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_never_meet_of_two_right_angles
-- name    : ParallelPostulate.Pairs.Figure.never_meet_of_two_right_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:47.603889+00:00
-- url     : https://prove2.me/theorems/eb6411f9-ba71-4f0a-98b4-a8274316d2c6
-- title:
--   Figure: never meet of two right angles
-- statement:
--   **Two right angles: the lines never meet.** If the side of `c1` is not zero, and the cross
--   product of the directions of `b` and `c` is zero, the two lines have no point in common.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L228-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L228-L239

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
open ParallelPostulate.Pairs
variable {K : Type*} [CommRing K]
open ParallelPostulate.Pairs.Figure

theorem ParallelPostulate.Pairs.Figure.never_meet_of_two_right_angles (F : Figure K)
    (hc : F.a.side F.c.one ≠ 0) (hsum : cross F.b.dir F.c.dir = 0) (t u : K) :
    F.b.pt t ≠ F.c.pt u := by sorry
