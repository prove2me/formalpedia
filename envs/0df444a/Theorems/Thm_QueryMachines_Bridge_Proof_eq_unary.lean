-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_eq_unary
-- name    : QueryMachines.Bridge.Proof.eq_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:01:12.09869+00:00
-- url     : https://prove2.me/theorems/2c6900f1-c027-4486-bdf4-79735e1863ea
-- title:
--   Proof: eq unary
-- statement:
--   A list of units is its length in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L25-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L25-L25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels

theorem QueryMachines.Bridge.Proof.eq_unary (b : U) : b = unary b.length := by sorry
