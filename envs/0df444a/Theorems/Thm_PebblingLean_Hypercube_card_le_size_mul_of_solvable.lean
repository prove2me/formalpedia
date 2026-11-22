-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_card_le_size_mul_of_solvable
-- name    : PebblingLean.Hypercube.card_le_size_mul_of_solvable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:50.981059+00:00
-- url     : https://prove2.me/theorems/273e550f-8d6b-477d-b96c-bf94ab571a7d
-- title:
--   Hypercube: card le size mul of solvable
-- statement:
--   Formal version of the averaged weight inequality
--   `|Q_n| ≤ |D| (3/2)^n` for every solvable distribution `D`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L121-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L121-L126

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

theorem PebblingLean.Hypercube.card_le_size_mul_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    (Fintype.card (HypercubeVertex n) : ℚ) ≤
      (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by sorry
