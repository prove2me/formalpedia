-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_size_done
-- name    : QueryMachines.Tower.Toy.size_done
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:02:45.121855+00:00
-- url     : https://prove2.me/theorems/d2c303b7-4743-4dea-884f-46399da1eaa5
-- title:
--   Toy: size done
-- statement:
--   When it is done.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L36-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L36-L36

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

theorem QueryMachines.Tower.Toy.size_done (l v : ℕ) : size ((l, Sum.inr (Sum.inr (Sum.inr v))) : ℕ × Ph) = l.size + v.size + 5 := by sorry
