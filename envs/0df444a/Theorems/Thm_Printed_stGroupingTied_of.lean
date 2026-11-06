-- Prove2me | Theorems.Thm_Printed_stGroupingTied_of
-- name    : Printed.stGroupingTied_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:14:58.685839+00:00
-- url     : https://prove2.me/theorems/a2725e2a-edf6-49dd-964b-3618c0f29ec2
-- title:
--   Printed: st Grouping Tied of
-- statement:
--   Lemma 1 for the algorithm of its proof, from a proof of «a good grouping exists … fix the first
--   good one», the run of the search and «so the value equals Z».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Grouping.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Grouping.lean#L31-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingProcs
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_GroupingPoly
import Mathlib.Tactic
import Definitions.Def_Printed_Grouping
set_option autoImplicit false
section
section
open Printed
open QueryMachines

theorem Printed.stGroupingTied_of (hS : Eight.ViaGrouping.StSearch) (hStops : Exits.StSearchStops) (hV : Value.StValueEqualsZ) : StGroupingTied := by sorry
