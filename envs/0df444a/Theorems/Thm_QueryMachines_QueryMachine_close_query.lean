-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_query
-- name    : QueryMachines.QueryMachine.close_query
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:14:36.196704+00:00
-- url     : https://prove2.me/theorems/8c24a51f-30b8-4a83-9806-d8eb943efc6a
-- title:
--   Query Machine: close query
-- statement:
--   A single query becomes one step that looks the answer up.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L44-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L44-L46

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

theorem QueryMachines.QueryMachine.close_query [HasSize α] [HasSize A] (h : α → Q) (O : Q → Option A) :
    (query h : QueryMachine Q A α A).close O = Stepped.ofOption fun a => O (h a) := by sorry
