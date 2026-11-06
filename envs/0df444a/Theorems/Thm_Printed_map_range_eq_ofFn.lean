-- Prove2me | Theorems.Thm_Printed_map_range_eq_ofFn
-- name    : Printed.map_range_eq_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:44.211055+00:00
-- url     : https://prove2.me/theorems/7363981a-7282-4361-a147-090093a27e30
-- title:
--   Printed: map range eq of Fn
-- statement:
--   A list written with `List.range` and the same list written with `List.ofFn`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingProcs.lean#L30-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingProcs.lean#L30-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingProcs
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_map_range_eq_ofFn
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight Eight.SecNetworks QueryMachines QueryMachines.QueryMachine

theorem Printed.map_range_eq_ofFn {α : Type} {g : ℕ} (F : ℕ → α) (f : Fin g → α) (h : ∀ a : Fin g, F a.val = f a) : (List.range g).map F = List.ofFn f := by sorry
