-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_ite
-- name    : QueryMachines.QueryMachine.close_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:15:47.335891+00:00
-- url     : https://prove2.me/theorems/88da66c1-c53f-47c1-baad-74778d34d66f
-- title:
--   Query Machine: close ite
-- statement:
--   `close` commutes with `ite`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L115-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L115-L116

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

theorem QueryMachines.QueryMachine.close_ite (p : α → Bool) (M N : QueryMachine Q A α β) (O : Q → Option A) :
    (ite p M N).close O = Stepped.ite p (M.close O) (N.close O) := by sorry
