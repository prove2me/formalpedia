-- Prove2me | Theorems.Thm_QueryMachines_Tower_rout_none
-- name    : QueryMachines.Tower.rout_none
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:47:33.59982+00:00
-- url     : https://prove2.me/theorems/bdbaf7b9-ac5e-46df-a3da-e83fbae4342d
-- title:
--   Tower: rout none
-- statement:
--   While the running activation has not halted, the whole has not.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L32-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L32-L35

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

theorem QueryMachines.Tower.rout_none {s : M.σ} (K : List M.σ) (h : M.out s = none) : rout M (s :: K) = none := by sorry
