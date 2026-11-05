-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
-- name    : QueryMachines.QueryMachine.close_mapAsk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:14:39.541659+00:00
-- url     : https://prove2.me/theorems/e22182a7-480d-41da-9009-3c9f90e3002c
-- title:
--   Query Machine: close map Ask
-- statement:
--   Rewriting the queries is rewriting the oracle.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L49-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L49-L53

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

theorem QueryMachines.QueryMachine.close_mapAsk (h : Q → Q') (M : QueryMachine Q A α β) (O : Q' → Option A) :
    (mapAsk h M).close O = M.close fun x => O (h x) := by sorry
