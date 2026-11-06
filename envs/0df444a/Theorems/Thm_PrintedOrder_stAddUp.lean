-- Prove2me | Theorems.Thm_PrintedOrder_stAddUp
-- name    : PrintedOrder.stAddUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:49:36.779728+00:00
-- url     : https://prove2.me/theorems/b66b9076-142f-4ab6-b450-81c7ab86a7a7
-- title:
--   Printed Order: st Add Up
-- statement:
--   **«no two of which share a satisfying assignment, so that their numbers of satisfying
--   assignments add up»**, for every formula ψ and every list L of formulas, on n variables: if no
--   assignment satisfies two formulas at different places of L, and an assignment satisfies ψ exactly if
--   it satisfies some formula of L, then the number of satisfying assignments of ψ is the sum of those
--   of the formulas of L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L64-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L64-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitCount_Disjoint
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_AddUp
set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount

theorem PrintedOrder.stAddUp : StAddUp := by sorry
