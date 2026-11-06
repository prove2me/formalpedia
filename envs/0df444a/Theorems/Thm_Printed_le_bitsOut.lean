-- Prove2me | Theorems.Thm_Printed_le_bitsOut
-- name    : Printed.le_bitsOut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:18.462864+00:00
-- url     : https://prove2.me/theorems/bf092dd0-c6d4-4324-8231-3b24c1ccb1ae
-- title:
--   Printed: le bits Out
-- statement:
--   P·⌊2g/K⌋ + g²B ≤ B'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L255-L262
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L255-L262

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
variable {C : Type} [HasSize C] {g K : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Printed.le_bitsOut {K : ℕ} (hK0 : 0 < K) (g P B : ℕ) : P * (2 * g / K) + g ^ 2 * B ≤ bitsOut K g P B := by sorry
