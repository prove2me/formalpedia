-- Prove2me | Theorems.Thm_Sat3_eq_of_slots
-- name    : Sat3.eq_of_slots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:33.62852+00:00
-- url     : https://prove2.me/theorems/f8254eb7-3313-49a8-96fd-c84ee00175c4
-- title:
--   Sat3: eq of slots
-- statement:
--   A clause of at most 3 literals is known by its first 3 slots.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Formula.lean#L18-L23
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Formula.lean#L18-L23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Math_Formula
set_option autoImplicit false
section
open Sat3

theorem Sat3.eq_of_slots {n : ℕ} {C D : List (Lit n)} (hC : C.length ≤ 3) (hD : D.length ≤ 3)
    (h : ∀ j < 3, C[j]? = D[j]?) : C = D := by sorry
