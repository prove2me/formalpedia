-- Prove2me | Theorems.Thm_TwoMachines_eq_of_halted
-- name    : TwoMachines.eq_of_halted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:54.69921+00:00
-- url     : https://prove2.me/theorems/322d6b08-d5f4-479a-a72a-136cc0826803
-- title:
--   Two Machines: eq of halted
-- statement:
--   If M is halted after i steps and reaches the halted configuration c after n steps, it is in c
--   after i steps already.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L61-L62

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

theorem TwoMachines.eq_of_halted {M : TM2ComputableAux Bool Bool} {c₀ c : M.tm.Cfg} {i n : ℕ} (hi : ((stay M)^[i] c₀).l = none) (hin : i ≤ n) (hn : (stay M)^[n] c₀ = c) : (stay M)^[i] c₀ = c := by sorry
