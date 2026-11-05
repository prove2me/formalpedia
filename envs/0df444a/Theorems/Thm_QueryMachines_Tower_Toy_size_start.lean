-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_size_start
-- name    : QueryMachines.Tower.Toy.size_start
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:02:41.183923+00:00
-- url     : https://prove2.me/theorems/5a844cd4-59db-4d34-a458-2b9e70b57df6
-- title:
--   Toy: size start
-- statement:
--   The size of the solver's state at the start.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L30-L30

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

theorem QueryMachines.Tower.Toy.size_start (l : ℕ) : size ((l, Sum.inl ()) : ℕ × Ph) = l.size + 3 := by sorry
