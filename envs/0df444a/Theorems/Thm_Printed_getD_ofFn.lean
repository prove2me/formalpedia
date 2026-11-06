-- Prove2me | Theorems.Thm_Printed_getD_ofFn
-- name    : Printed.getD_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:03:12.167765+00:00
-- url     : https://prove2.me/theorems/6e88eded-ed2a-4765-8c73-2b67be8056c8
-- title:
--   Printed: get D of Fn
-- statement:
--   The entry number a of a list written with `List.ofFn`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L40-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Eight_Fact_getD_ofFn
import Theorems.Thm_Eight_MulOut_getD_ofFn
import Theorems.Thm_Groundwork_Prog_NetE_getD_ofFn

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.getD_ofFn {α : Type} {g : ℕ} (f : Fin g → α) (a : Fin g) (d : α) : (List.ofFn f).getD a.val d = f a := by sorry
