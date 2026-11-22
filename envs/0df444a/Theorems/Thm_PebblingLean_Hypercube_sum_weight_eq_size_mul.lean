-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_weight_eq_size_mul
-- name    : PebblingLean.Hypercube.sum_weight_eq_size_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:52.10969+00:00
-- url     : https://prove2.me/theorems/43bd914f-3d8f-456b-b762-07317d3b870a
-- title:
--   Hypercube: sum weight eq size mul
-- statement:
--   The double sum of weights factors as `|D| * (3/2)^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L99-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L99-L117

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

theorem PebblingLean.Hypercube.sum_weight_eq_size_mul {n : ℕ} (D : Pebbling (HypercubeVertex n)) :
    (∑ target : HypercubeVertex n, weight dist D target)
      = (size D : ℚ) * ((3 : ℚ) / 2) ^ n := by sorry
