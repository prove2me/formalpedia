-- Prove2me | Theorems.Thm_PrintedOrder_eth_and_seth_false
-- name    : PrintedOrder.eth_and_seth_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:11:07.563752+00:00
-- url     : https://prove2.me/theorems/fb6f94f7-424e-491c-a8ea-b138b607252c
-- title:
--   Printed Order: eth and seth false
-- statement:
--   **Corollary 5**, in the wording of PaperSentencesStatement.lean: `endThroughImplication` on
--   `stThreeSatFamily`, `stHosted` and `SplitSat.stTiedThreeTM`. For k > 3 the way is: Theorem 2 gives
--   the family, the implication gives the machine for k-SAT, a Turing machine simulates it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L88-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L88-L88

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
import Theorems.Thm_SplitSat_eth_and_seth_false

set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal

theorem PrintedOrder.eth_and_seth_false : EthAndSethAgain := by sorry
