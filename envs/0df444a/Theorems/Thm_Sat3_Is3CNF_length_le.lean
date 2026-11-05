-- Prove2me | Theorems.Thm_Sat3_Is3CNF_length_le
-- name    : Sat3.Is3CNF.length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:23:23.287987+00:00
-- url     : https://prove2.me/theorems/858d0c87-1053-48e7-a73d-6ce02611587b
-- title:
--   Is3 CNF: length le
-- statement:
--   An instance on n variables has at most (2n+1)³ clauses, so its code is polynomially long.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Formula.lean#L26-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Formula.lean#L26-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Math_Formula
set_option autoImplicit false
section
open Sat3

theorem Sat3.Is3CNF.length_le {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : φ.length ≤ (2 * n + 1) ^ 3 := by sorry
