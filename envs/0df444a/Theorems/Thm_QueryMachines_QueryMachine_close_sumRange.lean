-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
-- name    : QueryMachines.QueryMachine.close_sumRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:16:57.46303+00:00
-- url     : https://prove2.me/theorems/06b8ed4a-200f-4845-9347-d392e468df60
-- title:
--   Query Machine: close sum Range
-- statement:
--   `close` commutes with `sumRange`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L132-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L132-L133

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

theorem QueryMachines.QueryMachine.close_sumRange [HasSize α] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) ℤ) (O : Q → Option A) :
    (sumRange N M).close O = Stepped.sumRange N (M.close O) := by sorry
