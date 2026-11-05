-- Prove2me | Theorems.Thm_QueryMachines_Tower_rstep_step
-- name    : QueryMachines.Tower.rstep_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:49:26.433613+00:00
-- url     : https://prove2.me/theorems/2e70dcfb-b7a7-4192-8543-f35d98895bd0
-- title:
--   Tower: rstep step
-- statement:
--   An own step of the running activation.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L50-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)

theorem QueryMachines.Tower.rstep_step {s : M.σ} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = none) : rstep M (s :: K) = M.step s :: K := by sorry
