-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_meet_eq
-- name    : ParallelPostulate.Pairs.Figure.meet_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:26.501438+00:00
-- url     : https://prove2.me/theorems/e3c53652-3d5f-4b0c-979e-30bf77baaf07
-- title:
--   Figure: meet eq
-- statement:
--   Where `b` and `c` meet, when the cross product of their directions is not zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L281-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L281-L290

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
variable {K : Type*} [Field K]

theorem ParallelPostulate.Pairs.Figure.meet_eq (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) :
    F.b.pt (cross F.a.dir F.c.dir / cross F.b.dir F.c.dir)
      = F.c.pt (cross F.a.dir F.b.dir / cross F.b.dir F.c.dir) := by sorry
