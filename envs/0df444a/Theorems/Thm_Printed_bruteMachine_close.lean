-- Prove2me | Theorems.Thm_Printed_bruteMachine_close
-- name    : Printed.bruteMachine_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:45:42.264597+00:00
-- url     : https://prove2.me/theorems/b1e443c5-d880-4ea2-b6d8-0c5369bdfefa
-- title:
--   Printed: brute Machine close
-- statement:
--   Brute force: with the tables built in, `bruteMachine` is `Groundwork.brute`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L35-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L35-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Comb
import Mathlib.Tactic
import Definitions.Def_Printed_Close
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
variable {Q A C : Type}

theorem Printed.bruteMachine_close (K : ℕ) (O : TableQuery → Option ℤ) :
    (bruteMachine K).close O = brute K (fun c : List Unit × List Unit => c.1.length) nilC ((askTable : QueryMachine TableQuery ℤ ((List Unit × List Unit) × IQ) ℤ).close O) := by sorry
