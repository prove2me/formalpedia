-- Prove2me | Theorems.Thm_SplitCount_length_leafF_le
-- name    : SplitCount.length_leafF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:31:35.983709+00:00
-- url     : https://prove2.me/theorems/5229b362-ce2f-49ba-bf46-c03651251575
-- title:
--   Split Count: length leaf F le
-- statement:
--   The formula of a node is not longer than with clauses appended to the side list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L90-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L90-L92

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width

theorem SplitCount.length_leafF_le (t : PFml) (x : CNode) : (leafF x).length ≤ (leafF (withSide t x)).length := by sorry
