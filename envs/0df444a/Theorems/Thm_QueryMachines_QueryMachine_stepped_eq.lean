-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_stepped_eq
-- name    : QueryMachines.QueryMachine.stepped_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:27.492448+00:00
-- url     : https://prove2.me/theorems/4e724830-7d4e-4838-b85f-e4b0ad497305
-- title:
--   Query Machine: stepped eq
-- statement:
--   Two step machines with the same type of states and the same measure of size are equal if init,
--   step and out agree at every argument.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L235-L240
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L235-L240

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}

theorem QueryMachines.QueryMachine.stepped_eq {σ : Type} [HasSize σ] {i i' : α → σ} {st st' : σ → σ} {o o' : σ → Option β} (h1 : ∀ a, i a = i' a)
    (h2 : ∀ s, st s = st' s) (h3 : ∀ s, o s = o' s) : (⟨σ, i, st, o⟩ : Stepped α β) = ⟨σ, i', st', o'⟩ := by sorry
