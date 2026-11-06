-- Prove2me | Theorems.Thm_Printed_levelDiv_poly
-- name    : Printed.levelDiv_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:31.861471+00:00
-- url     : https://prove2.me/theorems/51ceea84-59e2-42f3-b100-e36e89210cf8
-- title:
--   Printed: level Div poly
-- statement:
--   The division at the end has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L76-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L76-L79

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

theorem Printed.levelDiv_poly (g : ℕ) :
    (QueryMachine.lift (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)) : QueryMachine TableQuery ℤ ((List Unit × List Unit) × ℤ) ℤ).PolyTimeSteps := by sorry
