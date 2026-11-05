-- Prove2me | Theorems.Thm_TwoMachines_everyTwoMachinesCanBeChosenBetween
-- name    : TwoMachines.everyTwoMachinesCanBeChosenBetween
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:49:46.975819+00:00
-- url     : https://prove2.me/theorems/3d8f78a3-6ccb-4367-a5d8-a5d68041787e
-- title:
--   Two Machines: every Two Machines Can Be Chosen Between
-- statement:
--   A polynomial-time test on the input can choose between any two machines with finite alphabets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L204-L226
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L204-L226

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

theorem TwoMachines.everyTwoMachinesCanBeChosenBetween : EveryTwoMachinesCanBeChosenBetween := by sorry
