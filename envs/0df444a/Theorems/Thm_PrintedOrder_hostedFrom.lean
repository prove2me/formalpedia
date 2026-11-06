-- Prove2me | Theorems.Thm_PrintedOrder_hostedFrom
-- name    : PrintedOrder.hostedFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:32.939506+00:00
-- url     : https://prove2.me/theorems/62351827-781a-4bd4-a0bb-4dc551ced950
-- title:
--   Printed Order: hosted From
-- statement:
--   **k-SAT on Turing machines from any family of procedures for 3-SAT**, from the implication for
--   machines cut into steps, which is a hypothesis. The implication is taken at δ/2; a Turing machine
--   simulates the machine that it gives, with polynomial overhead.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L51-L55

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

theorem PrintedOrder.hostedFrom : SplitSat.StImplication → StHosted := by sorry
