-- Prove2me | Theorems.Thm_Printed_answer_close
-- name    : Printed.answer_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:45:12.37326+00:00
-- url     : https://prove2.me/theorems/730a44cc-de08-4c79-a16e-5d953e61890b
-- title:
--   Printed: answer close
-- statement:
--   The four procedures as one machine: `close` goes to each of them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L41-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L41-L43

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

theorem Printed.answer_close (Np : ProcsQ Q A C) (O : Q → Option A) : Np.answer.close O = answerOf (Np.close O) := by sorry
