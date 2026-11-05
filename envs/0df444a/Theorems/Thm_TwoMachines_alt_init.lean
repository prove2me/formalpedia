-- Prove2me | Theorems.Thm_TwoMachines_alt_init
-- name    : TwoMachines.alt_init
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:51:11.560447+00:00
-- url     : https://prove2.me/theorems/7573dda2-db03-4e07-a8d2-aa8d33f240fd
-- title:
--   Two Machines: alt init
-- statement:
--   The alternation starts with the pair of the start configurations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L48-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L48-L50

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

theorem TwoMachines.alt_init (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (x : List Bool) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).init x = (K₁.rep (start M₁ (pre₁ x)), K₂.rep (start M₂ (pre₂ x))) := by sorry
