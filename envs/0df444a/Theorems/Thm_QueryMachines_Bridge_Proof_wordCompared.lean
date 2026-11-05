-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_wordCompared
-- name    : QueryMachines.Bridge.Proof.wordCompared
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:24:25.114984+00:00
-- url     : https://prove2.me/theorems/62fe23ba-37fd-446b-8492-f83765750f5f
-- title:
--   Proof: word Compared
-- statement:
--   Whether the word of a value has at most as many symbols as a padding string has units is decided
--   in polynomial time, for every type and every coding.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L229-L230
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L229-L230

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_CountedToPadded_Compare
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Turing Groundwork Groundwork.TM Groundwork.PolyT

theorem QueryMachines.Bridge.Proof.wordCompared (α : Type) [Enc α] : PolyT fun p : List Unit × α => decide (len p.2 ≤ p.1.length) := by sorry
