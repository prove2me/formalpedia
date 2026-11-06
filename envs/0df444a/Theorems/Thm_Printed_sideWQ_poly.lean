-- Prove2me | Theorems.Thm_Printed_sideWQ_poly
-- name    : Printed.sideWQ_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:51:10.450323+00:00
-- url     : https://prove2.me/theorems/5c14aca2-19df-4d80-b19f-f1f4d8127bcb
-- title:
--   Printed: side WQ poly
-- statement:
--   The weight of a row or column, computed with queries to the tables, has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L36-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L36-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_ToTuring_Poly_GridSide
import Mathlib.Tactic
import Definitions.Def_Printed_LevelPoly
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

theorem Printed.sideWQ_poly (g : ℕ) (tr : Bool) : (sideWQ g tr fun c : List Unit × List Unit => c.1.length).PolyTimeSteps := by sorry
