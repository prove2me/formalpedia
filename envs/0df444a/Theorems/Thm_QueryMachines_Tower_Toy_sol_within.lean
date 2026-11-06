-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_sol_within
-- name    : QueryMachines.Tower.Toy.sol_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:03:34.264318+00:00
-- url     : https://prove2.me/theorems/e58787b9-df4d-43ea-a383-103adafd441b
-- title:
--   Toy: sol within
-- statement:
--   The solver, with its calls and queries answered as specified, returns the value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L43-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L43-L82

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
import Theorems.Thm_Groundwork_PolyT_elim

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork Groundwork.Prog

theorem QueryMachines.Tower.Toy.sol_within (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ) (hG : (spec ℓ0 M0).Good c f) (tc tq : ℕ) :
    Sol.Within ((spec ℓ0 M0).oracle noG c f) (Sum.elim (fun _ => tc) (Sum.elim (fun _ => tq) noW)) c (TS c.1 tc tq) (SS ℓ0 M0) (sumF c.1 f) := by sorry
