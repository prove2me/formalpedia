-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_card_le_sum_weight_of_solvable
-- name    : PebblingLean.Hypercube.card_le_sum_weight_of_solvable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:47.554819+00:00
-- url     : https://prove2.me/theorems/3006f053-c2f9-4c38-be95-bc936464b258
-- title:
--   Hypercube: card le sum weight of solvable
-- statement:
--   Summing the target-wise lower bound over all targets gives
--   `|Q_n| ≤ ∑_t W_t(D)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L57-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L57-L67

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

theorem PebblingLean.Hypercube.card_le_sum_weight_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    (Fintype.card (HypercubeVertex n) : ℚ) ≤
      ∑ target : HypercubeVertex n, weight dist D target := by sorry
