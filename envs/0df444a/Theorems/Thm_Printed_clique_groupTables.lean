-- Prove2me | Theorems.Thm_Printed_clique_groupTables
-- name    : Printed.clique_groupTables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:55.499955+00:00
-- url     : https://prove2.me/theorems/38a93760-c61e-4208-bcb4-4cd36c9a4723
-- title:
--   Printed: clique group Tables
-- statement:
--   The clique with these tables is the clique of the groups.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L120-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L120-L122

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

theorem Printed.clique_groupTables {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) :
    (clique K L fun w => groupTables N P B hK0 x L w.val) = Value.groupClique (asked.close (netOracle N)) (netInput N P B) N hK0 x L := by sorry
