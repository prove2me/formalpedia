-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_bind
-- name    : QueryMachines.QueryMachine.close_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:14:58.68956+00:00
-- url     : https://prove2.me/theorems/61bc235c-2f06-4641-b83f-6c95365f1e6d
-- title:
--   Query Machine: close bind
-- statement:
--   `close` commutes with `bind`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L64-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L64-L74

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

theorem QueryMachines.QueryMachine.close_bind [HasSize α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) (O : Q → Option A) :
    (bind M N).close O = Stepped.bind (M.close O) (N.close O) := by sorry
