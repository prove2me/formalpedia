-- Prove2me | Theorems.Thm_TwoMachines_alt_out_running
-- name    : TwoMachines.alt_out_running
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:42.818215+00:00
-- url     : https://prove2.me/theorems/8e4e7195-a24b-4f62-b58b-a1d686a3be55
-- title:
--   Two Machines: alt out running
-- statement:
--   As long as neither machine has halted the alternation has no result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L38-L40

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
set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}

theorem TwoMachines.alt_out_running (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) {c₁ : M₁.tm.Cfg} {c₂ : M₂.tm.Cfg} (h₁ : c₁.l ≠ none) (h₂ : c₂.l ≠ none) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).out (K₁.rep c₁, K₂.rep c₂) = none := by sorry
