-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
-- name    : QueryMachines.QueryMachine.close_foldRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:16:28.898148+00:00
-- url     : https://prove2.me/theorems/87715268-fb99-47d4-927a-35e3c0e89b3c
-- title:
--   Query Machine: close fold Range
-- statement:
--   `close` commutes with `foldRange`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L128-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L128-L129

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

theorem QueryMachines.QueryMachine.close_foldRange [HasSize α] [HasSize γ] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) β) (g : γ → ℕ → β → γ) (c₀ : α → γ) (O : Q → Option A) :
    (foldRange N M g c₀).close O = Stepped.foldRange N (M.close O) g c₀ := by sorry
