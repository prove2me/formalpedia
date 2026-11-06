-- Prove2me | Theorems.Thm_PrintedOrder_stepAddsFrom
-- name    : PrintedOrder.stepAddsFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:57:03.347282+00:00
-- url     : https://prove2.me/theorems/7d3f2973-902f-4e2c-a4f9-023fc61a0825
-- title:
--   Printed Order: step Adds From
-- statement:
--   The same for one step of the tree, from two statements taken as hypotheses: the two children of
--   a node share no satisfying assignment and an assignment satisfies the node exactly if it satisfies
--   one of them (`SplitCount.StDisjoint`); then the numbers add up (`StAddUp`, for the list of the two
--   children).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L121-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L121-L127

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

theorem PrintedOrder.stepAddsFrom : SplitCount.StDisjoint → StAddUp → StStepAdds := by sorry
