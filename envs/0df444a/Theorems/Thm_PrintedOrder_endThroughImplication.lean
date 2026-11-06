-- Prove2me | Theorems.Thm_PrintedOrder_endThroughImplication
-- name    : PrintedOrder.endThroughImplication
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:11:03.376337+00:00
-- url     : https://prove2.me/theorems/3630b9a6-0718-45d5-880b-67a1cc806eed
-- title:
--   Printed Order: end Through Implication
-- statement:
--   **Corollary 5 in the order of its printed proof**, from three statements taken as hypotheses:
--   «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false.» At k = 3 the Turing
--   machine is that of `SplitSat.StTiedThreeTM` («Theorem 2 gives s_3=0»); at k > 3 the family of
--   `StThreeSatFamily` is handed to `StHosted`; then the general `SatK.sTM_eq_zero_of`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L65-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L65-L83

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

theorem PrintedOrder.endThroughImplication : StThreeSatFamily → StHosted → SplitSat.StTiedThreeTM → SplitSat.ThreeSatStatement := by sorry
