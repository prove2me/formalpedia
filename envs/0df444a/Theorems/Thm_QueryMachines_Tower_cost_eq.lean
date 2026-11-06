-- Prove2me | Theorems.Thm_QueryMachines_Tower_cost_eq
-- name    : QueryMachines.Tower.cost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:48:18.99906+00:00
-- url     : https://prove2.me/theorems/9eb8a96f-d8a0-4b37-9cf2-06f5a85fb12b
-- title:
--   Tower: cost eq
-- statement:
--   The cost of the tower at depth l is the cost of the solver with the price of a call made at
--   depth l.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L55-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Chain.lean#L55-L55

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

theorem QueryMachines.Tower.cost_eq (l t : ℕ) : cost TS TI l t = TS l (callCost TS TI l t) t := by sorry
