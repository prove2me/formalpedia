-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_optBind
-- name    : QueryMachines.QueryMachine.close_optBind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:16:15.758515+00:00
-- url     : https://prove2.me/theorems/65910c14-50bd-4fda-b111-bcaa82ea5945
-- title:
--   Query Machine: close opt Bind
-- statement:
--   `close` commutes with `optBind`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L123-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L123-L125

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

theorem QueryMachines.QueryMachine.close_optBind [HasSize α] [HasSize β] (M : QueryMachine Q A α (Option ι)) (N : QueryMachine Q A (α × ι) β) (dflt : α → β) (O : Q → Option A) :
    (optBind M N dflt).close O = Stepped.optBind (M.close O) (N.close O) dflt := by sorry
