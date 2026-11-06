-- Prove2me | Theorems.Thm_PrintedOrder_stStepAdds
-- name    : PrintedOrder.stStepAdds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:47.39076+00:00
-- url     : https://prove2.me/theorems/b536dbba-2ec8-4e80-bfc1-3af27297da6f
-- title:
--   Printed Order: st Step Adds
-- statement:
--   The number of satisfying assignments of a node is the sum of those of its two children:
--   `stepAddsFrom` on the proofs of its two hypotheses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L131-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L131-L131

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

theorem PrintedOrder.stStepAdds : StStepAdds := by sorry
