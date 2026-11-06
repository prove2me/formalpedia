-- Prove2me | Theorems.Thm_Printed_onFormula_poly
-- name    : Printed.onFormula_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:27.139198+00:00
-- url     : https://prove2.me/theorems/58cf9041-61ab-4942-af40-18afc1ecc00d
-- title:
--   Printed: on Formula poly
-- statement:
--   A machine for networks with polynomial-time steps, on the network of Φ: polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L52-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L52-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

theorem Printed.onFormula_poly (g k : ℕ) (NM : NetMachine) (hN : NM.PolyTimeSteps) : Nonempty (IsPolyT (networkOnSteps g NM (formulaProcs g k))) := by sorry
