-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_dir
-- name    : ParallelPostulate.Pairs.Figure.reverse_dir
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:08.994292+00:00
-- url     : https://prove2.me/theorems/493e53d5-fbd3-49db-9c82-4319977e7ee3
-- title:
--   Figure: reverse dir
-- statement:
--   The Figure construction uses the reverse dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L255-L256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L255-L256

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

theorem ParallelPostulate.Pairs.Figure.reverse_dir (F : Figure K) : F.reverse.a.dir = -F.a.dir := by sorry
