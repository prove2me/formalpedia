-- Prove2me | Theorems.Thm_Printed_poly_le
-- name    : Printed.poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:35.992205+00:00
-- url     : https://prove2.me/theorems/1811cce0-9749-43d8-b79d-a06b1db11b00
-- title:
--   Printed: poly le
-- statement:
--   D·X + M·X^k ≤ c·X^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L289-L292
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L289-L292

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.poly_le {D M k c X : ℕ} (hX : 1 ≤ X) (hk : k ≤ c) (h1 : 1 ≤ c) (hc : D + M ≤ c) : D * X + M * X ^ k ≤ c * X ^ c := by sorry
