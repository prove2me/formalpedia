-- Prove2me | Theorems.Thm_SatFree_allZero
-- name    : SatFree.allZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:16:02.16496+00:00
-- url     : https://prove2.me/theorems/0ad3acfb-83ca-4629-8868-c1f3b253ddb8
-- title:
--   Sat Free: all Zero
-- statement:
--   **Corollary 5**: «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false», for
--   the numbers s_k defined with the code that does not depend on k. It is `FreeCode.allZeroFrom`
--   applied to `FreeCode.stTiedThree` (Theorem 2) and `FreeCode.stTied` (the reduction).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Main.lean#L144-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Main.lean#L144-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_Order
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Behind
import Definitions.Def_FreeCode_Brute
import Definitions.Def_FreeCode_Tied
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Main
set_option autoImplicit false
section
section
open SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal

theorem SatFree.allZero : AllZero := by sorry
