-- Prove2me | Theorems.Thm_TwoMachines_alt_runs
-- name    : TwoMachines.alt_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:15.933448+00:00
-- url     : https://prove2.me/theorems/7df80fa8-b2fd-4d4c-95d6-9ce095998354
-- title:
--   Two Machines: alt runs
-- statement:
--   If M₁ puts out y₁ on `pre₁ x` within t₁ steps, M₂ puts out y₂ on `pre₂ x` within t₂ steps and
--   the two results agree, the alternation ends on x with that result within min(t₁, t₂) steps, on
--   states of size linear in |pre₁ x| + |pre₂ x| + min(t₁, t₂).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L82-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/TwoMachines/Main.lean#L82-L136

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

theorem TwoMachines.alt_runs (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) {x y₁ y₂ : List Bool} {t₁ t₂ : ℕ}
    (h₁ : Outputs M₁ (pre₁ x) y₁ t₁) (h₂ : Outputs M₂ (pre₂ x) y₂ t₂) (he : post₁ y₁ = post₂ y₂) :
    (alt K₁ K₂ pre₁ pre₂ post₁ post₂).Runs x (min t₁ t₂)
      (K₁.a * ((pre₁ x).length + 1) + K₁.a * min t₁ t₂ + (K₂.a * ((pre₂ x).length + 1) + K₂.a * min t₁ t₂)) (post₁ y₁) := by sorry
