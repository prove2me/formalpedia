-- Prove2me | Theorems.Thm_Printed_bitsOut_le_Bp
-- name    : Printed.bitsOut_le_Bp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:37.023478+00:00
-- url     : https://prove2.me/theorems/161576bb-0d6a-4c8d-a1ad-50a48ed8e46e
-- title:
--   Printed: bits Out le Bp
-- statement:
--   B' = ⌈2gP/K⌉ + g²B, written with a quotient of natural numbers, is at most the same written with
--   the ceiling of a real number (they are equal).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L93-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L93-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.bitsOut_le_Bp {K : ℕ} (hK0 : 0 < K) (g P B : ℕ) : bitsOut K g P B ≤ Cost.Bp K g P B := by sorry
