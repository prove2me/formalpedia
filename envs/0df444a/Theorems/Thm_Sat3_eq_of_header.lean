-- Prove2me | Theorems.Thm_Sat3_eq_of_header
-- name    : Sat3.eq_of_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:22.605931+00:00
-- url     : https://prove2.me/theorems/6fcda710-a7ce-40f1-bdd3-2432f3662012
-- title:
--   Sat3: eq of header
-- statement:
--   The header 1ⁿ 0 delimits itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Formula.lean#L34-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Formula.lean#L34-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Math_Formula
set_option autoImplicit false
section
open Sat3

theorem Sat3.eq_of_header : ∀ {n m : ℕ} {l l' : List Bool},
    List.replicate n true ++ false :: l = List.replicate m true ++ false :: l' → n = m ∧ l = l'
  := by sorry
