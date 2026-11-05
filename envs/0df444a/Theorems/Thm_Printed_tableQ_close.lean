-- Prove2me | Theorems.Thm_Printed_tableQ_close
-- name    : Printed.tableQ_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:44:27.867198+00:00
-- url     : https://prove2.me/theorems/e77ff05c-c5ca-48d3-8509-f8d51e243c65
-- title:
--   Printed: table Q close
-- statement:
--   One entry W̃_γ(Θ): with the oracle built in, `tableQ` is `Eight.ViaGrouping.tableM` on the
--   procedures with the oracle built in.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L24-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L24-L26

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

theorem Printed.tableQ_close [HasSize C] (K g : ℕ) (Np : ProcsQ Q A C) (O : Q → Option A) : (tableQ K g Np).close O = tableM K g (Np.close O) := by sorry
