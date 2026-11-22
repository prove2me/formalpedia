-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_cross
-- name    : ParallelPostulate.Pairs.Figure.reverse_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:11.815786+00:00
-- url     : https://prove2.me/theorems/ecced1e2-e592-4235-9202-6e20b2021e2c
-- title:
--   Figure: reverse cross
-- statement:
--   The Figure construction uses the reverse cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L258-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L258-L261

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

theorem ParallelPostulate.Pairs.Figure.reverse_cross (F : Figure K) :
    cross F.reverse.b.dir F.reverse.c.dir = -cross F.b.dir F.c.dir := by sorry
