-- Prove2me | Theorems.Thm_Printed_asked_isNetworkP
-- name    : Printed.asked_isNetworkP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:40.7452+00:00
-- url     : https://prove2.me/theorems/ece4e220-f693-4736-bbe2-023032b5ced3
-- title:
--   Printed: asked is Network P
-- statement:
--   **Definition 2(iii) by queries.** The four procedures «ask», with the oracle of the network N
--   built in, give N in the context `netInput N P B`, each within one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L75-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L75-L143

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

theorem Printed.asked_isNetworkP {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) :
    IsNetworkP (asked.close (netOracle N)) (netInput N P B) N P B 1 (size (netInput N P B) + 2 * size g + 4 * P + B + 4) := by sorry
