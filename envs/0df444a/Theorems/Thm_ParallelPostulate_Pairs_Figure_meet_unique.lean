-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_meet_unique
-- name    : ParallelPostulate.Pairs.Figure.meet_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:09.932879+00:00
-- url     : https://prove2.me/theorems/f5ae6e66-e6e8-49f4-bdf4-e7194f6222b0
-- title:
--   Figure: meet unique
-- statement:
--   And they meet at one point only.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L293-L311
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L293-L311

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

theorem ParallelPostulate.Pairs.Figure.meet_unique (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) {t u t' u' : K}
    (h : F.b.pt t = F.c.pt u) (h' : F.b.pt t' = F.c.pt u') : t = t' ∧ u = u' := by sorry
