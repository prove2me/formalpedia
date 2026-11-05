-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
-- name    : QueryMachines.QueryMachine.close_foldWhile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:15:24.588095+00:00
-- url     : https://prove2.me/theorems/73a75a44-5dc4-4385-aa37-96ef1adcfd4c
-- title:
--   Query Machine: close fold While
-- statement:
--   `close` commutes with the loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L77-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L77-L87

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

theorem QueryMachines.QueryMachine.close_foldWhile [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : QueryMachine Q A τ β)
    (g : γ → τ → β → γ) (c₀ : α → γ) (O : Q → Option A) :
    (foldWhile start nxt M g c₀).close O = Stepped.foldWhile start nxt (M.close O) g c₀ := by sorry
