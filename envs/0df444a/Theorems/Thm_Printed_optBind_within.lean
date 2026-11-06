-- Prove2me | Theorems.Thm_Printed_optBind_within
-- name    : Printed.optBind_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:42.196058+00:00
-- url     : https://prove2.me/theorems/1a18f68d-2c25-4860-8d51-d27f0a009a5a
-- title:
--   Printed: opt Bind within
-- statement:
--   First a step machine R, which asks nothing; if its result is some i, then N on (a, i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L79-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L79-L87

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

theorem Printed.optBind_within {Q A α ι β : Type} [HasSize α] [HasSize β] {R : Stepped α (Option ι)} {N : QueryMachine Q A (α × ι) β} {dflt : α → β} {O : Q → Option A} {w : Q → ℕ} {a : α} {i : ι}
    {t T S S' : ℕ} {b : β} (h : R.Runs a t S (some i)) (h' : N.Within O w (a, i) T S' b) :
    (QueryMachine.optBind (QueryMachine.lift R) N dflt).Within O w a (t + 1 + T) (max (size a + S) (S' + 1) + 1) b := by sorry
