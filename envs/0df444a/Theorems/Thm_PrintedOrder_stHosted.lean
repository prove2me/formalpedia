-- Prove2me | Theorems.Thm_PrintedOrder_stHosted
-- name    : PrintedOrder.stHosted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:12:11.287114+00:00
-- url     : https://prove2.me/theorems/2885ab4c-b423-4606-8c3b-253a62785f04
-- title:
--   Printed Order: st Hosted
-- statement:
--   **k-SAT on Turing machines from any family of procedures for 3-SAT, through the implication**:
--   `hostedFrom` on `SplitSat.stImplication`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L59-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L59-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitSat_Main
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Deciding
set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal

theorem PrintedOrder.stHosted : StHosted := by sorry
