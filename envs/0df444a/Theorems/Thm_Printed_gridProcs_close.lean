-- Prove2me | Theorems.Thm_Printed_gridProcs_close
-- name    : Printed.gridProcs_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:46:08.8907+00:00
-- url     : https://prove2.me/theorems/4444a34c-4b89-4212-a0cc-1f2a8ffffe83
-- title:
--   Printed: grid Procs close
-- statement:
--   The two networks of ι: with the tables built in, `gridProcs` is `Eight.ViaGrouping.levelProcs`,
--   except that its bound `B` is B₁ = gB + g²λ + 1 of the proof of Proposition 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L47-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L47-L51

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

theorem Printed.gridProcs_close (g : ℕ) (tr : Bool) (O : TableQuery → Option ℤ) :
    (gridProcs g tr).close O = { levelProcs g tr (gridPsi g tr) (fun c : List Unit × List Unit => c.1.length) (askTable.close O) with
      B := fun c => g * c.1.2.length + g ^ 2 * c.1.1.length + 1 } := by sorry
