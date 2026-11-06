-- Prove2me | Theorems.Thm_Printed_length_lt_size
-- name    : Printed.length_lt_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:08:58.243787+00:00
-- url     : https://prove2.me/theorems/0378a078-327e-4ffe-b327-82835f73deb6
-- title:
--   Printed: length lt size
-- statement:
--   A list is shorter than its size.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L95-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L95-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_length_lt_size
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

theorem Printed.length_lt_size {α : Type} [HasSize α] (l : List α) : l.length < size l := by sorry
