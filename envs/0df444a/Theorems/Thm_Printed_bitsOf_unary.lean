-- Prove2me | Theorems.Thm_Printed_bitsOf_unary
-- name    : Printed.bitsOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:50:51.734526+00:00
-- url     : https://prove2.me/theorems/228eb17b-c6b3-44c7-a9f9-4b581ad98941
-- title:
--   Printed: bits Of unary
-- statement:
--   B is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L33-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L33-L33

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

theorem Printed.bitsOf_unary : Unary fun c : List Unit × List Unit => c.2.length := by sorry
