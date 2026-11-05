-- Prove2me | Theorems.Thm_QueryMachines_stPolyPlug
-- name    : QueryMachines.stPolyPlug
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:57:59.69633+00:00
-- url     : https://prove2.me/theorems/c3b86a96-1f46-41a1-8fe6-57de9e15bea1
-- title:
--   Query Machines: st Poly Plug
-- statement:
--   `StPolyPlug` holds: `plug` of a machine with query access and polynomial-time steps and a step
--   machine with polynomial-time steps has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Poly.lean#L374-L374
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Poly.lean#L374-L374

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Poly
set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine

theorem QueryMachines.stPolyPlug : StPolyPlug := by sorry
