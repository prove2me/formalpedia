-- Prove2me | Theorems.Thm_Printed_mapIn_within
-- name    : Printed.mapIn_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:05:48.521349+00:00
-- url     : https://prove2.me/theorems/20b844a4-7cba-4200-84ec-ccea8e9981a3
-- title:
--   Printed: map In within
-- statement:
--   A function applied to the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L73-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L73-L76

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

theorem Printed.mapIn_within {Q A α β γ : Type} {f : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {c : γ} (h : M.Within O w (f a) T S c) :
    (QueryMachine.mapIn f M).Within O w a T S c := by sorry
