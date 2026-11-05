-- Prove2me | Theorems.Thm_Printed_levelMachine_close
-- name    : Printed.levelMachine_close
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:43:14.440281+00:00
-- url     : https://prove2.me/theorems/8fdb9391-24bb-47ce-ae7b-7489cf0f09b4
-- title:
--   Printed: level Machine close
-- statement:
--   The algorithm of the proof of Proposition 3: with the tables built in, it is the loop of
--   `Eight.ViaGrouping.levelAlgP` over the machine `groupingMachine` of Lemma 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L62-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Close.lean#L62-L68

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

theorem Printed.levelMachine_close (K g : ℕ) (M : CliqueMachine) (O : TableQuery → Option ℤ) :
    (levelMachine K g M).close O = Stepped.bind
      (Stepped.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
        (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g (groupingMachine K g M) ((gridProcs g false).close O))
          (networkOnSteps g (groupingMachine K g M) ((gridProcs g true).close O))))
      (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)) := by sorry
