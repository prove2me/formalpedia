-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_cost_toy
-- name    : QueryMachines.Tower.Toy.cost_toy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:04:25.01928+00:00
-- url     : https://prove2.me/theorems/dddd946d-efa7-435d-9b9f-c02fdf89f044
-- title:
--   Toy: cost toy
-- statement:
--   The recursion of the costs, solved.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L121-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L121-L128

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

theorem QueryMachines.Tower.Toy.cost_toy : ∀ l t : ℕ, cost TS TI l t + 5 = 2 ^ l * (t + 2 * l + 5)
  := by sorry
