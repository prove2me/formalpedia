-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_cand_eq
-- name    : QueryMachines.Bridge.Proof.cand_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:43.703197+00:00
-- url     : https://prove2.me/theorems/4056f9ee-53f4-4bb6-9c5b-d440a231d478
-- title:
--   Proof: cand eq
-- statement:
--   The entry for ℓ within the length of b, by what `kf` computes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L41-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean#L41-L47

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

theorem QueryMachines.Bridge.Proof.cand_eq {K : ℕ → ℕ} {kf : U × U → Option U} (hk : ComputesLevels K kf) (b : U) {l : ℕ} (h : l ≤ b.length) :
    cand kf b l = if K l ≤ b.length then some (unary l, (unary l, unary (K l))) else none := by sorry
