-- Prove2me | Theorems.Thm_TwoMachines_exists_length_le
-- name    : TwoMachines.exists_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:29.262976+00:00
-- url     : https://prove2.me/theorems/cb255a2d-fab8-4f8b-a403-f3cb3e5b20cb
-- title:
--   Two Machines: exists length le
-- statement:
--   The length of the value of a polynomial-time function on bit strings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L181-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L181-L186

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

theorem TwoMachines.exists_length_le {pre : List Bool → List Bool} (hpre : PolyT pre) : ∃ c : ℕ, ∀ x : List Bool, (pre x).length ≤ c * (3 * x.length + 2 + 1) ^ c := by sorry
