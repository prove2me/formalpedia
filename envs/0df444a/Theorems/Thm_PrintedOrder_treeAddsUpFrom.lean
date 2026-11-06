-- Prove2me | Theorems.Thm_PrintedOrder_treeAddsUpFrom
-- name    : PrintedOrder.treeAddsUpFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:19.785108+00:00
-- url     : https://prove2.me/theorems/f537c718-9ec7-4606-99a4-daa61c7f77a0
-- title:
--   Printed Order: tree Adds Up From
-- statement:
--   **The numbers of the leaves add up to that of the given formula**, from four statements taken as
--   hypotheses: no two leaves share a satisfying assignment (`SplitCount.StDisjointLeaves`); an
--   assignment satisfies a node exactly if it satisfies some leaf below it (`StCovered`); the root has
--   the satisfying assignments of the given formula (`StRootSame`); then the numbers add up (`StAddUp`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L100-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L100-L111

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

theorem PrintedOrder.treeAddsUpFrom : SplitCount.StDisjointLeaves → StCovered → StRootSame → StAddUp → StTreeAddsUp := by sorry
