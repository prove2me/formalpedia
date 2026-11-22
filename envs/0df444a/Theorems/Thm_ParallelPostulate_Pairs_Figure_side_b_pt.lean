-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_side_b_pt
-- name    : ParallelPostulate.Pairs.Figure.side_b_pt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:28.59905+00:00
-- url     : https://prove2.me/theorems/266acf23-bdeb-4cd3-9481-6a96915fe4dd
-- title:
--   Figure: side b pt
-- statement:
--   The Figure construction uses the side b pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L221-L224
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L221-L224

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

theorem ParallelPostulate.Pairs.Figure.side_b_pt (F : Figure K) (t : K) :
    F.a.side (F.b.pt t) = t * cross F.a.dir F.b.dir := by sorry
