-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_visit_total
-- name    : QueryMachines.Bridge.Proof.visit_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:24:17.149648+00:00
-- url     : https://prove2.me/theorems/895ade79-2881-4fb8-aa96-952c0ff543fe
-- title:
--   Proof: visit total
-- statement:
--   A round keeps the sum of the count and the symbols still to be visited.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L135-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L135-L138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_CountedToPadded_Compare
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Turing Groundwork Groundwork.TM Groundwork.PolyT

theorem QueryMachines.Bridge.Proof.visit_total (s : List V × ℕ) : (visit s).2 + total (visit s).1 = s.2 + total s.1 := by sorry
