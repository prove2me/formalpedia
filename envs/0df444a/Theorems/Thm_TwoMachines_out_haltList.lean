-- Prove2me | Theorems.Thm_TwoMachines_out_haltList
-- name    : TwoMachines.out_haltList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:51:40.423145+00:00
-- url     : https://prove2.me/theorems/ed6e9970-5c75-438d-b4b0-642021743b09
-- title:
--   Two Machines: out halt List
-- statement:
--   What a coding reads from the halted configuration with y on the output stack.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L65-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L65-L68

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}

theorem TwoMachines.out_haltList {M : TM2ComputableAux Bool Bool} (K : Coding M) (y : List Bool) : K.out (K.rep (haltList M.tm (y.map M.outputAlphabet.invFun))) = some y := by sorry
