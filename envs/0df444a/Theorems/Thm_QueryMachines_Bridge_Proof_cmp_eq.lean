-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_cmp_eq
-- name    : QueryMachines.Bridge.Proof.cmp_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:23:53.111192+00:00
-- url     : https://prove2.me/theorems/e3b77801-d654-4641-b82d-0cd7a43e254c
-- title:
--   Proof: cmp eq
-- statement:
--   The comparison decides whether the word is at most as long as the padding string.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L175-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L175-L194

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

theorem QueryMachines.Bridge.Proof.cmp_eq (p : List Unit × V) : cmp p = decide ((code p.2).length ≤ p.1.length) := by sorry
