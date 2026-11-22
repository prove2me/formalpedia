-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
-- name    : PebblingLean.Pebbling.fibersDistribution_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:29.808309+00:00
-- url     : https://prove2.me/theorems/059064c4-e991-45a0-b51b-afc16863cec2
-- title:
--   Pebbling: fibers Distribution apply
-- statement:
--   The Pebbling construction uses the fibers Distribution apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L59-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Product.lean#L59-L61

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}

theorem PebblingLean.Pebbling.fibersDistribution_apply (F : W → Pebbling V) (x : V) (z : W) :
    fibersDistribution F (x, z) = F z x := by sorry

attribute [defeq] PebblingLean.Pebbling.fibersDistribution_apply
