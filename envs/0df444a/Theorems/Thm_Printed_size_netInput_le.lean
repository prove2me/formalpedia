-- Prove2me | Theorems.Thm_Printed_size_netInput_le
-- name    : Printed.size_netInput_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:17.188957+00:00
-- url     : https://prove2.me/theorems/ecc62244-2608-45d9-92cc-7f50b599fe73
-- title:
--   Printed: size net Input le
-- statement:
--   The input of Definition 2(iii), all numbers in unary, has size linear in P + B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L146-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L146-L167

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

theorem Printed.size_netInput_le {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) : size (netInput N P B) ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B) := by sorry
