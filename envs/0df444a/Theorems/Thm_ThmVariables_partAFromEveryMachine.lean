-- Prove2me | Theorems.Thm_ThmVariables_partAFromEveryMachine
-- name    : ThmVariables.partAFromEveryMachine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:42:34.770037+00:00
-- url     : https://prove2.me/theorems/76ac3191-bb19-4300-810a-6a6576c61e60
-- title:
--   Thm Variables: part AFrom Every Machine
-- statement:
--   Theorem D (a) in the form that says that there is a machine (`PartA`) follows from the form for
--   every machine (`PartAForEveryMachine`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/EveryMachine.lean#L58-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/EveryMachine.lean#L58-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ThmVariables_PartA
import Definitions.Def_ThmVariables_EveryMachine
set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms

theorem ThmVariables.partAFromEveryMachine : PartAFromEveryMachine := by sorry
