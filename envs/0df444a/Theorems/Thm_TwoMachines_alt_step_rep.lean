-- Prove2me | Theorems.Thm_TwoMachines_alt_step_rep
-- name    : TwoMachines.alt_step_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:51:35.877383+00:00
-- url     : https://prove2.me/theorems/3f0b5dee-805d-4cf8-b00b-e6ab01161733
-- title:
--   Two Machines: alt step rep
-- statement:
--   One step of the alternation advances both configurations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L43-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L43-L45

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
import Theorems.Thm_CircuitLowerBound_Tab_Enc_step

set_option autoImplicit false
section
section
open TwoMachines
open Turing Groundwork Wrap CircuitLowerBound.Tab
variable {M₁ M₂ : TM2ComputableAux Bool Bool}

theorem TwoMachines.alt_step_rep (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (c₁ : M₁.tm.Cfg) (c₂ : M₂.tm.Cfg) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).step (K₁.rep c₁, K₂.rep c₂) = (K₁.rep (stay M₁ c₁), K₂.rep (stay M₂ c₂)) := by sorry
