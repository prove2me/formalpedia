-- Prove2me | Theorems.Thm_TwoMachines_size_rep_le
-- name    : TwoMachines.size_rep_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:51:26.58377+00:00
-- url     : https://prove2.me/theorems/dd29735f-f06e-44a9-9bcd-7406d11f57bb
-- title:
--   Two Machines: size rep le
-- statement:
--   The size of the value for the configuration after i steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L71-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L71-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_TwoMachines_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_TwoMachines_Main
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}

theorem TwoMachines.size_rep_le {M : TM2ComputableAux Bool Bool} (K : Coding M) (x : List Bool) {i t : ℕ} (hi : i ≤ t) : size (K.rep ((stay M)^[i] (start M x))) ≤ K.a * (x.length + 1) + K.a * t := by sorry
