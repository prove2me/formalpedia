-- Prove2me | Theorems.Thm_QueryMachines_Tower_Toy_inn_within
-- name    : QueryMachines.Tower.Toy.inn_within
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:03:52.372204+00:00
-- url     : https://prove2.me/theorems/063ec393-c651-48b7-943b-16730dcee6b3
-- title:
--   Toy: inn within
-- statement:
--   The procedure, with the caller's tables, returns the entries of the callee's tables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L85-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Toy/Meets.lean#L85-L100

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

theorem QueryMachines.Tower.Toy.inn_within (ℓ0 M0 : ℕ) (c : ℕ × Bool) (f : List Bool → Option ℕ) (c' : ℕ × Bool) (hG : (spec ℓ0 M0).Good c f) (hch : (spec ℓ0 M0).Child c f c') (q : List Bool) (a : ℕ)
    (ht : (spec ℓ0 M0).tab c' f q = some a) (tq : ℕ) : Inn.Within (Sum.elim f noG) (Sum.elim (fun _ => tq) noW) (c', q) (TI c'.1 tq) (SI ℓ0 M0) a := by sorry
