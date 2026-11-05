-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_reaches_size
-- name    : QueryMachines.Bridge.Proof.reaches_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:14:30.019265+00:00
-- url     : https://prove2.me/theorems/ad8c6b98-7f2b-433e-976c-32b2a140f17d
-- title:
--   Proof: reaches size
-- statement:
--   The first state of a run is within the bound on the sizes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L29-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/RunFor.lean#L29-L32

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
omit [Enc N.σ] [Carried N.σ]

theorem QueryMachines.Bridge.Proof.reaches_size {s : N.σ} {t : ℕ} (h : N.Reaches S b s t) : size s ≤ S := by sorry
