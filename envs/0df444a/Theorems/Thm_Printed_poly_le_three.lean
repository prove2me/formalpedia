-- Prove2me | Theorems.Thm_Printed_poly_le_three
-- name    : Printed.poly_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:11.418755+00:00
-- url     : https://prove2.me/theorems/f7f60fed-752a-4978-a69a-b543fb0ae495
-- title:
--   Printed: poly le three
-- statement:
--   D·X + M·X^k + M'·X^k' ≤ c·X^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L106-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L106-L110

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

theorem Printed.poly_le_three {D M M' k k' c X : ℕ} (hX : 1 ≤ X) (hk : k ≤ c) (hk' : k' ≤ c) (h1 : 1 ≤ c) (hc : D + M + M' ≤ c) : D * X + M * X ^ k + M' * X ^ k' ≤ c * X ^ c := by sorry
