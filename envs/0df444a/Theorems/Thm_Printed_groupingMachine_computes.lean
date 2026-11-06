-- Prove2me | Theorems.Thm_Printed_groupingMachine_computes
-- name    : Printed.groupingMachine_computes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:30:27.744835+00:00
-- url     : https://prove2.me/theorems/3444aff5-0be8-4420-9afc-dd3e295b4d2e
-- title:
--   Printed: grouping Machine computes
-- statement:
--   The bound of Lemma 1 for the algorithm of its proof, on networks on [g], for every g ≥ K for
--   which the search finds a good grouping (hypothesis `hS`; for g = 3K⁸ this is
--   `Eight.ViaGrouping.StSearch`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L170-L242
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L170-L242

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.groupingMachine_computes (hStops : Exits.StSearchStops) (hE : StEntryCost) (hV : Value.StValueEqualsZ) (hSub : StSubst) {K g : ℕ} {e : ℝ} {M : CliqueMachine} {Cc : ℕ} (hK0 : 0 < K) (hg : 0 < g) (h0 : 0 ≤ e)
    (hM : AchievedBy M Cc K e)
    (hS : ∀ (N : Net g) (P B : ℕ), N.Is P B → ∃ x < K ^ g, (List.range (K ^ g)).find? (fun x => goodP K g (asked.close (netOracle N)) (netInput N P B, x)) = some x ∧ Good N.c P (Paper.grouping (g := g) hK0 x)) :
    ∃ C₁ : ℕ, ComputesNetworks (groupingMachine K g M) C₁ g K e := by sorry
