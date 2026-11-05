-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_fold_halted
-- name    : QueryMachines.Bridge.Proof.fold_halted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:15.751892+00:00
-- url     : https://prove2.me/theorems/98c53394-e66d-41a4-9495-076e846ea0bf
-- title:
--   Proof: fold halted
-- statement:
--   A halted state stays to the end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L40-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L40-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F
variable {α β : Type} {N : Stepped α β} [Enc N.σ] [Carried N.σ] {S room : ℕ} {b : β}

theorem QueryMachines.Bridge.Proof.fold_halted (hS : 7 * S + 2 ≤ room) {s : N.σ} (h1 : N.out s = some b) (h2 : size s ≤ S) (fuel : U) :
    fuel.foldl (fun (s : Option N.σ) _ => cutAt room (s.map (stay N))) (some s) = some s := by sorry
