-- Prove2me | Theorems.Thm_Printed_c_le
-- name    : Printed.c_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:49.471169+00:00
-- url     : https://prove2.me/theorems/a4394bc3-b4a2-47c8-bf5b-2283e3e30f14
-- title:
--   Printed: c le
-- statement:
--   c_{a,b} ≤ P, by (i) of Definition 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L70-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L70-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Eight_SecNetworks_Net_c_le
import Theorems.Thm_Groundwork_SatNet_c_le

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.c_le {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) : N.c a b ≤ P := by sorry
