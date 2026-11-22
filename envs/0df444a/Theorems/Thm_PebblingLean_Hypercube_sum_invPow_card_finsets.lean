-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_invPow_card_finsets
-- name    : PebblingLean.Hypercube.sum_invPow_card_finsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:45.77658+00:00
-- url     : https://prove2.me/theorems/7eff4a93-a688-48bb-8dcb-c086a65e755b
-- title:
--   Hypercube: sum inv Pow card finsets
-- statement:
--   The finite-subset identity behind the inner hypercube weight sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L70-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L70-L82

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Weight
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.sum_invPow_card_finsets (n : ℕ) :
    (∑ s : Finset (Fin n), (1 : ℚ) / (2 : ℚ) ^ s.card) = ((3 : ℚ) / 2) ^ n := by sorry
