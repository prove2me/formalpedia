-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_subst
-- name    : QueryMachines.QueryMachine.close_subst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:22.255594+00:00
-- url     : https://prove2.me/theorems/bd8667d1-0f9d-484f-8d79-a6cacbfde586
-- title:
--   Query Machine: close subst
-- statement:
--   Building the outer oracle into a substitution is plugging in the answering machine with that
--   oracle built in.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L244-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L244-L252

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}

theorem QueryMachines.QueryMachine.close_subst [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O' : Q' → Option A') :
    (M.subst N).close O' = M.plug (N.close O') := by sorry
