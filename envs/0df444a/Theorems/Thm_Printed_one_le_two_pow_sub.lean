-- Prove2me | Theorems.Thm_Printed_one_le_two_pow_sub
-- name    : Printed.one_le_two_pow_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:51.29864+00:00
-- url     : https://prove2.me/theorems/3306f632-3d38-42a3-97c5-6beeb7dc50db
-- title:
--   Printed: one le two pow sub
-- statement:
--   1 ≤ 2^B − 1 for B ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L200-L203
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L200-L203

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

theorem Printed.one_le_two_pow_sub {B : ℕ} (hB : 1 ≤ B) : (1 : ℤ) ≤ 2 ^ B - 1 := by sorry
