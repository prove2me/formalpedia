-- Prove2me | Theorems.Thm_PrintedOrder_card_some
-- name    : PrintedOrder.card_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:45:32.932388+00:00
-- url     : https://prove2.me/theorems/35d131bd-21c4-4574-b211-8951d709db25
-- title:
--   Printed Order: card some
-- statement:
--   If no assignment satisfies two formulas at different places of the list L, the number of
--   assignments to x₀ … xₙ₋₁ that satisfy some formula of L is the sum of the numbers of satisfying
--   assignments of the formulas of L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L46-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L46-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_AddUp
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount
open Classical

theorem PrintedOrder.card_some (n : ℕ) : ∀ L : List Fml, (L.Pairwise fun y z => ∀ a : ℕ → Bool, ¬(Holds a y ∧ Holds a z)) →
    (Finset.univ.filter fun b : Fin n → Bool => ∃ y ∈ L, Holds (ext b) y).card = (L.map fun y => cntN n y).sum
  := by sorry
