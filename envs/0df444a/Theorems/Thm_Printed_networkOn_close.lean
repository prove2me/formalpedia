-- Prove2me | Theorems.Thm_Printed_networkOn_close
-- name    : Printed.networkOn_close
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:44:44.40406+00:00
-- url     : https://prove2.me/theorems/b9d7e865-b14f-4527-af7c-ac4294c73730
-- title:
--   Printed: network On close
-- statement:
--   A machine for networks run on procedures that may ask: with the oracle built in, its queries are
--   answered by the procedures with the oracle built in.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L55-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L55-L58

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

theorem Printed.networkOn_close [HasSize C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) (O : Q → Option A) :
    (networkOn g NM Np).close O = networkOnSteps g NM (Np.close O) := by sorry
