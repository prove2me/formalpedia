-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_both_reaches_inr
-- name    : QueryMachines.QueryMachine.both_reaches_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:44:12.03225+00:00
-- url     : https://prove2.me/theorems/3a37ab31-06f8-4641-8c4f-5a51d9f627da
-- title:
--   Query Machine: both reaches inr
-- statement:
--   The second machine of `both`, run inside.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L92-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L92-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Stepped_both_reaches_inr

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.both_reaches_inr [HasSize α] [HasSize β] {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {c : γ} {s : N.σ}
    (h : N.Reaches O S c s t L) : (both M N).Reaches O (size b + S + 1) (b, c) (.inr (b, s)) t L := by sorry
