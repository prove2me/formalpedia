-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Dim_side_through
-- name    : ParallelPostulate.Pairs.Dim.side_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:49.677191+00:00
-- url     : https://prove2.me/theorems/0bad6633-5ba7-4a4b-8e7a-8342695ff06f
-- title:
--   Dim: side through
-- statement:
--   Along the dimension from `A` to `C`, the side changes evenly from the side of `A` to the
--   side of `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L171-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L171-L174

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

theorem ParallelPostulate.Pairs.Dim.side_through (L : Dim K) (A C : K × K) (u : K) :
    L.side ((Dim.mk A C).pt u) = (1 - u) * L.side A + u * L.side C := by sorry
