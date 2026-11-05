-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_gated
-- name    : QueryMachines.QueryMachine.close_gated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:16:55.777182+00:00
-- url     : https://prove2.me/theorems/b035a1af-4e5c-409d-9a24-38ce6f06603e
-- title:
--   Query Machine: close gated
-- statement:
--   `close` commutes with `gated`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L140-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L140-L142

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

theorem QueryMachines.QueryMachine.close_gated [HasSize α] (M : QueryMachine Q A α Bool) (N : QueryMachine Q A α ℤ) (O : Q → Option A) :
    (gated M N).close O = Eight.SecNetworks.gated (M.close O) (N.close O) := by sorry
