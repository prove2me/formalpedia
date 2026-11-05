-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_cutAt_some
-- name    : QueryMachines.Bridge.Proof.cutAt_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:01:00.505176+00:00
-- url     : https://prove2.me/theorems/79a8ec64-7c39-409f-829c-bdc68bb9ff2b
-- title:
--   Proof: cut At some
-- statement:
--   A state of size at most S is not cut.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F
variable {α β : Type} {N : Stepped α β} [Enc N.σ] [Carried N.σ] {S room : ℕ} {b : β}

theorem QueryMachines.Bridge.Proof.cutAt_some (hS : 7 * S + 2 ≤ room) {s : N.σ} (h : size s ≤ S) : cutAt room (some s) = some s := by sorry
