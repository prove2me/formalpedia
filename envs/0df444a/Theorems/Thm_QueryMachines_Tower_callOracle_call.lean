-- Prove2me | Theorems.Thm_QueryMachines_Tower_callOracle_call
-- name    : QueryMachines.Tower.callOracle_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:18.086534+00:00
-- url     : https://prove2.me/theorems/2ee2035e-008f-4406-9cad-1cb3f2c18ce6
-- title:
--   Tower: call Oracle call
-- statement:
--   A call of a good input of smaller depth is answered by its value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L78-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L78-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Chain
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Ctx Q G A : Type} (P : Spec Ctx Q A) (TS : ℕ → ℕ → ℕ → ℕ) (TI : ℕ → ℕ → ℕ) (c0 : Ctx) (f0 : Q → Option A) (tq : ℕ)

theorem QueryMachines.Tower.callOracle_call {Q A α β : Type} (O : Q → Option A) {Good : α → Prop} (val : α → β) {dep : α → ℕ} {a a' : α} (h : Good a' ∧ dep a' < dep a) :
    callOracle O Good val dep a (Sum.inr a') = some (Sum.inr (val a')) := by sorry
