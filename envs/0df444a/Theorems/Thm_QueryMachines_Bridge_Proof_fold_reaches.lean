-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_fold_reaches
-- name    : QueryMachines.Bridge.Proof.fold_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:17.228436+00:00
-- url     : https://prove2.me/theorems/ee71855d-23b3-4158-b8c9-c0fd26d8009f
-- title:
--   Proof: fold reaches
-- statement:
--   From a state from which N halts with b within T steps, the fold ends in a state with the result
--   b once the fuel has at least T units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L50-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L50-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F
variable {α β : Type} {N : Stepped α β} [Enc N.σ] [Carried N.σ] {S room : ℕ} {b : β}

theorem QueryMachines.Bridge.Proof.fold_reaches (hS : 7 * S + 2 ≤ room) {s : N.σ} {T : ℕ} (h : N.Reaches S b s T) : ∀ fuel : U, T ≤ fuel.length →
    (fuel.foldl (fun (s : Option N.σ) _ => cutAt room (s.map (stay N))) (some s)).bind N.out = some b := by sorry
