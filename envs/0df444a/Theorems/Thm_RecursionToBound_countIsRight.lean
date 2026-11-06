-- Prove2me | Theorems.Thm_RecursionToBound_countIsRight
-- name    : RecursionToBound.countIsRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:21:38.508567+00:00
-- url     : https://prove2.me/theorems/cce84956-bde4-4a95-ba7d-3b09d91db2a1
-- title:
--   Recursion To Bound: count Is Right
-- statement:
--   The function is right in the range of Theorem D (a).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Main.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Main.lean#L38-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_OneOutput
import Definitions.Def_RecursionToBound_Exponent
import Definitions.Def_RecursionToBound_Cert_Top
import Definitions.Def_RecursionToBound_Guard
import Definitions.Def_RecursionToBound_Tree
import Definitions.Def_RecursionToBound_Correct
import Definitions.Def_RecursionToBound_End
import Definitions.Def_RecursionToBound_Main
set_option autoImplicit false
section
section
open RecursionToBound

theorem RecursionToBound.countIsRight : CountIsRight := by sorry
