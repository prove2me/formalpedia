-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_take_unary
-- name    : QueryMachines.Bridge.Proof.take_unary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:05.269202+00:00
-- url     : https://prove2.me/theorems/200b84a2-a2df-45bb-bf76-dc9a6d67d7a3
-- title:
--   Proof: take unary
-- statement:
--   The first ℓ units of b are ℓ in unary, for ℓ within the length of b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L28-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L28-L29

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

theorem QueryMachines.Bridge.Proof.take_unary (b : U) {l : ℕ} (h : l ≤ b.length) : b.take l = unary l := by sorry
