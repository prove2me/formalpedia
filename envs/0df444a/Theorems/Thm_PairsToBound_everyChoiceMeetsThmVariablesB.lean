-- Prove2me | Theorems.Thm_PairsToBound_everyChoiceMeetsThmVariablesB
-- name    : PairsToBound.everyChoiceMeetsThmVariablesB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:59:31.353245+00:00
-- url     : https://prove2.me/theorems/8ab0985d-7c28-4bd7-8163-00324c0f4178
-- title:
--   Pairs To Bound: every Choice Meets Thm Variables B
-- statement:
--   **The main statement** (Step 6 of Appendix D): every machine that chooses, by the printed test,
--   between a machine with the conclusion of Theorem D (a) behind the front end and a machine that tries
--   all assignments meets the bound of Theorem D (b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Main.lean#L54-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Main.lean#L54-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_FrontEnd
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_TwoMachines_Main
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_PairsToBound_Main
set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms VariableBound.Paper
open Sat3 (CNF)

theorem PairsToBound.everyChoiceMeetsThmVariablesB : EveryChoiceMeetsThmVariablesB := by sorry
