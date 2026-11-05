-- Prove2me | Theorems.Thm_TwoMachines_everyTwoMachinesCanBeAlternated
-- name    : TwoMachines.everyTwoMachinesCanBeAlternated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:48:25.499535+00:00
-- url     : https://prove2.me/theorems/03293bdb-38a8-40af-9c9b-35bd59d8f4eb
-- title:
--   Two Machines: every Two Machines Can Be Alternated
-- statement:
--   Any two machines with finite alphabets can be run in alternation.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L189-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L189-L199

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

theorem TwoMachines.everyTwoMachinesCanBeAlternated : EveryTwoMachinesCanBeAlternated := by sorry
