-- Prove2me | Theorems.Thm_TwoMachines_exists_halt
-- name    : TwoMachines.exists_halt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:06.365624+00:00
-- url     : https://prove2.me/theorems/4b67fbaa-d313-454e-88ff-612165cef245
-- title:
--   Two Machines: exists halt
-- statement:
--   A run of M on x with output y within t steps: after some n ≤ t steps of the step that stays, M
--   is in the halted configuration with y on its output stack.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L54-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L54-L57

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

theorem TwoMachines.exists_halt {M : TM2ComputableAux Bool Bool} {x y : List Bool} {t : ℕ} (h : Outputs M x y t) :
    ∃ n ≤ t, (stay M)^[n] (start M x) = haltList M.tm (y.map M.outputAlphabet.invFun) := by sorry
