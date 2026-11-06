-- Prove2me | Theorems.Thm_Printed_firstLine_poly
-- name    : Printed.firstLine_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:25.221432+00:00
-- url     : https://prove2.me/theorems/d0c8c8ce-57e3-4de1-baa1-da2eed4b912e
-- title:
--   Printed: first Line poly
-- statement:
--   Line 6 keeps polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L201-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L201-L204

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

theorem Printed.firstLine_poly {Mc : Stepped Formula ℤ} (h : Nonempty (IsPolyT Mc)) : Nonempty (IsPolyT (Stepped.ite (fun Φ : Formula => Φ.isEmpty) (Stepped.const 1) Mc)) := by sorry
