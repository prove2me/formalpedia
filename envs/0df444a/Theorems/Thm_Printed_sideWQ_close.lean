-- Prove2me | Theorems.Thm_Printed_sideWQ_close
-- name    : Printed.sideWQ_close
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:46:23.046322+00:00
-- url     : https://prove2.me/theorems/1c8444be-cfd3-4926-a93f-e52b6e633ec2
-- title:
--   Printed: side WQ close
-- statement:
--   The weight of a row: with the tables built in, `sideWQ` is `Groundwork.Prog.sideWP`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L29-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L29-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Comb
import Mathlib.Tactic
import Definitions.Def_Printed_Close
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
variable {Q A C : Type}

theorem Printed.sideWQ_close [HasSize C] (g : ℕ) (tr : Bool) (lam : C → ℕ) (O : TableQuery → Option ℤ) :
    (sideWQ g tr lam).close O = sideWP g tr lam ((askTable : QueryMachine TableQuery ℤ (C × IQ) ℤ).close O) := by sorry
