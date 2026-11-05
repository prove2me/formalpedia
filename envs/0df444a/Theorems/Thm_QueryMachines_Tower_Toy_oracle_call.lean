-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_oracle_call
-- name    : QueryMachines.Tower.Toy.oracle_call
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:04:21.50679+00:00
-- url     : https://prove2.me/theorems/34301a24-f25f-4f43-a1d3-a5d4cf191702
-- title:
--   Toy: oracle call
-- statement:
--   A call one level down is answered by the sum over the strings that begin with the callee's bit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L39-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L39-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_TowerRuns
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Toy_Meets
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog

theorem QueryMachines.Tower.Toy.oracle_call (ℓ0 M0 l : ℕ) (b b' : Bool) (f : List Bool → Option ℕ) : (spec ℓ0 M0).oracle noG (l + 1, b) f (Sum.inl (l, b')) = some (sumF l fun q => f (b' :: q)) := by sorry
