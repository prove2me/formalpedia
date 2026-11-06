-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_len_cutAt_le
-- name    : QueryMachines.Bridge.Proof.len_cutAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:19.997849+00:00
-- url     : https://prove2.me/theorems/6b341fa4-3800-4f78-8dc9-2387cb37ea84
-- title:
--   Proof: len cut At le
-- statement:
--   The output of the cut has length at most `room + 2`: a value that is kept has length at most
--   `room`, and `none` has length at most 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L66-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L66-L70

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

theorem QueryMachines.Bridge.Proof.len_cutAt_le {γ : Type} [Enc γ] (room : ℕ) (x : Option γ) : len (cutAt room x) ≤ room + 2 := by sorry
