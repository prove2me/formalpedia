-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_sum_ite_nonzero_const
-- name    : PebblingLean.Pebbling.sum_ite_nonzero_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:19.154807+00:00
-- url     : https://prove2.me/theorems/f53dfbf4-0a12-4bc3-a808-16c48e4f16e4
-- title:
--   Pebbling: sum ite nonzero const
-- statement:
--   The Pebbling construction uses the sum ite nonzero const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L274-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L274-L284

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}

theorem PebblingLean.Pebbling.sum_ite_nonzero_const [Fintype V] (D : Pebbling V) (K : ℕ) :
    (∑ v : V, if D v = 0 then 0 else K) = supportSize D * K := by sorry
