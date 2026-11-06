-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_last_succ
-- name    : QueryMachines.Bridge.Proof.last_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:24.033468+00:00
-- url     : https://prove2.me/theorems/1319e888-ea13-4d38-8570-68fadf303c04
-- title:
--   Proof: last succ
-- statement:
--   The last entry among the first m + 1 numbers is that of m, if there is one, else the last among
--   the first m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L51-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L51-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_Groundwork_PolyT_filterMap
attribute [local fun_prop] Groundwork.PolyT.filterMap


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels

theorem QueryMachines.Bridge.Proof.last_succ (kf : U × U → Option U) (b : U) (m : ℕ) :
    ((List.range (m + 1)).filterMap (cand kf b)).getLast? = (cand kf b m).or ((List.range m).filterMap (cand kf b)).getLast? := by sorry
