-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_pickOf_eq
-- name    : QueryMachines.Bridge.Proof.pickOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:08.531216+00:00
-- url     : https://prove2.me/theorems/02d6ebc3-ecc6-4a9d-91eb-fe2a9ad17ea3
-- title:
--   Proof: pick Of eq
-- statement:
--   The program, written with `cand`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L84-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L84-L84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels

theorem QueryMachines.Bridge.Proof.pickOf_eq (kf : U × U → Option U) (K₀ : ℕ) (b : U) : pickOf kf K₀ b = (((List.range (b.length + 1)).filterMap (cand kf b)).getLast?).getD ([], ([], unary K₀)) := by sorry
