-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_visit_work
-- name    : QueryMachines.Bridge.Proof.visit_work
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:24:19.279904+00:00
-- url     : https://prove2.me/theorems/26e15088-c1b3-46d7-b184-5a9afb076ef7
-- title:
--   Proof: visit work
-- statement:
--   A round on a list that is not empty visits exactly one node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L141-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L141-L142

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

theorem QueryMachines.Bridge.Proof.visit_work (v : V) (r : List V) (c : ℕ) : work (visit (v :: r, c)).1 + 1 = work (v :: r) := by sorry
