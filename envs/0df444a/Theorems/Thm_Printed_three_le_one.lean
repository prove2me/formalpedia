-- Prove2me | Theorems.Thm_Printed_three_le_one
-- name    : Printed.three_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:12.906064+00:00
-- url     : https://prove2.me/theorems/8ae27cfe-485d-418a-84bc-07feafe11dce
-- title:
--   Printed: three le one
-- statement:
--   Of three conditions that exclude one another at most one holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L172-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L172-L174

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

theorem Printed.three_le_one (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] (hab : A → ¬B) (hac : A → ¬C) (hbc : B → ¬C) :
    (if A then 1 else 0) + (if B then 1 else 0) + (if C then 1 else 0) ≤ 1 := by sorry
