-- Prove2me | Theorems.Thm_Printed_levelLoop_poly
-- name    : Printed.levelLoop_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:53:34.633088+00:00
-- url     : https://prove2.me/theorems/b7d5d840-2097-4818-8d69-267fb848d47e
-- title:
--   Printed: level Loop poly
-- statement:
--   The loop over ι has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L66-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L66-L73

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

theorem Printed.levelLoop_poly (g : ℕ) (NM : NetMachine) (hN : NM.PolyTimeSteps) :
    (QueryMachine.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
      (QueryMachine.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOn g NM (gridProcs g false)) (networkOn g NM (gridProcs g true)))).PolyTimeSteps := by sorry
