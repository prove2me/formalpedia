-- Prove2me | Theorems.Thm_Printed_size_listOfFn_le
-- name    : Printed.size_listOfFn_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:06.322201+00:00
-- url     : https://prove2.me/theorems/01902a4f-e272-4754-ae7d-65091c6e9aa1
-- title:
--   Printed: size list Of Fn le
-- statement:
--   A list of g things of size at most M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L45-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L45-L51

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

theorem Printed.size_listOfFn_le {α : Type} [HasSize α] {g : ℕ} (f : Fin g → α) (M : ℕ) (h : ∀ a, size (f a) ≤ M) : size (List.ofFn f) ≤ g * (M + 1) + 1 := by sorry
