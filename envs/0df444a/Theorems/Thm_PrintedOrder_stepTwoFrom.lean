-- Prove2me | Theorems.Thm_PrintedOrder_stepTwoFrom
-- name    : PrintedOrder.stepTwoFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:12:58.729768+00:00
-- url     : https://prove2.me/theorems/37434687-1d5b-46e1-843b-d70ef66a158b
-- title:
--   Printed Order: step Two From
-- statement:
--   **Step 2 of the proof of Corollary 6**, from two statements taken as hypotheses: the numbers of
--   the leaves add up to that of the given formula (`StTreeAddsUp`), and the bounds on the tree
--   (`StBounds`, which has no sum). The proof only puts the pieces together: the sum is that of
--   `StTreeAddsUp` at the depth Dd·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Counting.lean#L69-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Counting.lean#L69-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_PrintedOrder_AddUp
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Counting
set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal

theorem PrintedOrder.stepTwoFrom : StTreeAddsUp → StBounds → SplitCount.StStepTwo := by sorry
