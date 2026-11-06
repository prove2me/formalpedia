-- Prove2me | Theorems.Thm_SplitCount_mem_leafF_withSide
-- name    : SplitCount.mem_leafF_withSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:31:45.184073+00:00
-- url     : https://prove2.me/theorems/af322f92-074b-4c83-87fe-12c4444cd059
-- title:
--   Split Count: mem leaf F with Side
-- statement:
--   A clause of the formula of a node is still there after clauses are appended to the side list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L95-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L95-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Tree
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width

theorem SplitCount.mem_leafF_withSide {t : PFml} {x : CNode} {C : PCl} (h : C ∈ leafF x) : C ∈ leafF (withSide t x) := by sorry
