-- Prove2me | Theorems.Thm_PrintedOrder_stTreeAddsUp
-- name    : PrintedOrder.stTreeAddsUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:43.612446+00:00
-- url     : https://prove2.me/theorems/1d4c9d17-14f4-41ac-b662-12ea9c44830b
-- title:
--   Printed Order: st Tree Adds Up
-- statement:
--   **The numbers of the leaves add up to that of the given formula**, for all thresholds, every
--   width and every depth of the cut: `treeAddsUpFrom` on the proofs of its four hypotheses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L115-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/AddUp.lean#L115-L115

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

theorem PrintedOrder.stTreeAddsUp : StTreeAddsUp := by sorry
