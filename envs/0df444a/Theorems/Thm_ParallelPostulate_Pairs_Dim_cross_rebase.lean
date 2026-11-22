-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Dim_cross_rebase
-- name    : ParallelPostulate.Pairs.Dim.cross_rebase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:48.28615+00:00
-- url     : https://prove2.me/theorems/6fc289a0-8ce3-47b8-bce6-9363497356c3
-- title:
--   Dim: cross rebase
-- statement:
--   The moved dimension has the direction of the dimension it was made from.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L159-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L159-L161

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
open ParallelPostulate.Pairs.Dim

theorem ParallelPostulate.Pairs.Dim.cross_rebase (L : Dim K) (P : K × K) : cross L.dir (L.rebase P).dir = 0 := by sorry
