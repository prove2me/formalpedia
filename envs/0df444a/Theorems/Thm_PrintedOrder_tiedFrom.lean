-- Prove2me | Theorems.Thm_PrintedOrder_tiedFrom
-- name    : PrintedOrder.tiedFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:13:57.221373+00:00
-- url     : https://prove2.me/theorems/901f3856-68ac-41d0-b2bb-3a8c66c46071
-- title:
--   Printed Order: tied From
-- statement:
--   **The tied statement of proof/consequences/SplitCount/ with step 2 as a hypothesis**: for every
--   k ≥ 1 and δ > 0 there are ℓ, τ, a Turing machine M with finite alphabets and numbers c, q such that
--   `COUNTsplit k ℓ τ` has polynomial-time steps and counts within c·2^{δn} steps, M simulates it with
--   polynomial overhead, and M counts the satisfying assignments of k-CNFs within ⌊c·2^{δn}⌋ steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Counting.lean#L112-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/PrintedOrder/Counting.lean#L112-L126

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

theorem PrintedOrder.tiedFrom : SplitCount.StStepTwo → SplitCount.StTiedTM := by sorry
