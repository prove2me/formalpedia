-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_branch
-- name    : QueryMachines.QueryMachine.close_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:15:58.093238+00:00
-- url     : https://prove2.me/theorems/35c8779b-57b8-4572-997e-ccb68783691a
-- title:
--   Query Machine: close branch
-- statement:
--   `close` commutes with `branch`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L90-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L90-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}

theorem QueryMachines.QueryMachine.close_branch (sel : α → α₁ ⊕ α₂) (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) (O : Q → Option A) :
    (branch sel M₁ M₂).close O = Stepped.branch sel (M₁.close O) (M₂.close O) := by sorry
