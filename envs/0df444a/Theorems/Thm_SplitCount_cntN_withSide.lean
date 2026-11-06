-- Prove2me | Theorems.Thm_SplitCount_cntN_withSide
-- name    : SplitCount.cntN_withSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:40:19.585872+00:00
-- url     : https://prove2.me/theorems/2c3151bd-37a8-45c2-86fc-12024de2dd6c
-- title:
--   Split Count: cnt N with Side
-- statement:
--   The clauses xᵢ ∨ ¬xᵢ on the side list do not change the number of satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L100-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L100-L112

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

theorem SplitCount.cntN_withSide (n m : ℕ) (x : CNode) : cntN n (leafF (withSide (taut m) x)) = cntN n (leafF x) := by sorry
