-- Prove2me | Theorems.Thm_PrintedOrder_stThreeSatFamily
-- name    : PrintedOrder.stThreeSatFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:11:39.355207+00:00
-- url     : https://prove2.me/theorems/0c3ee48c-8e6b-4885-bccd-3cf26705a9bc
-- title:
--   Printed Order: st Three Sat Family
-- statement:
--   **«Theorem 2 gives s_3=0», for machines cut into steps**: there is a family of procedures for
--   3-SAT, one for each exponent δ₃ > 0, each with polynomial-time steps, and each member is the machine
--   of Theorem 2 in its decision form without the part that reads the input, at some level ℓ and
--   threshold parameter τ. From `SplitSat.stCore3`, by choice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L41-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Deciding.lean#L41-L46

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

theorem PrintedOrder.stThreeSatFamily : StThreeSatFamily := by sorry
