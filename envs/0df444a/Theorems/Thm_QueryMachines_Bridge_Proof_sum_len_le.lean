-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_sum_len_le
-- name    : QueryMachines.Bridge.Proof.sum_len_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:24:05.228928+00:00
-- url     : https://prove2.me/theorems/64829768-49ef-403f-9866-6b00115232a6
-- title:
--   Proof: sum len le
-- statement:
--   The word of the list of trees has at most three times their symbols, and two more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L197-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L197-L204

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_CountedToPadded_Compare
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Turing Groundwork Groundwork.TM Groundwork.PolyT

theorem QueryMachines.Bridge.Proof.sum_len_le (w : List V) : (w.map fun a => len a + 2).sum ≤ 3 * total w := by sorry
