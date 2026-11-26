-- Prove2me | Theorems.Thm_UnboundedChain_f_bounds
-- name    : UnboundedChain.f_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:46:10.710909+00:00
-- url     : https://prove2.me/theorems/e53adb1c-0c8b-4e76-8fb6-4e070faaceb8
-- title:
--   Unbounded Chain: f bounds
-- statement:
--   `f` assigns a strict upper bound to each chain.
--
--   Source: https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L516-L520
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean#L516-L520

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α] [Inhabited α] [UnboundedChain α]
open UnboundedChain

theorem UnboundedChain.f_bounds : ∀ (C : Set α), IsChain (· ≤ ·) C → ∀ a ∈ C, a < f C := by sorry
