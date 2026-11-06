-- Prove2me | Theorems.Thm_Printed_networkOn_gridProcs_poly
-- name    : Printed.networkOn_gridProcs_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:53:31.409708+00:00
-- url     : https://prove2.me/theorems/e68f3316-f08d-4347-88e9-52202ca42ed6
-- title:
--   Printed: network On grid Procs poly
-- statement:
--   A machine for networks with polynomial-time steps, on the row network or the column network of
--   ι.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L46-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelPoly.lean#L46-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_ToTuring_Poly_GridSide
import Mathlib.Tactic
import Definitions.Def_Printed_LevelPoly
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

theorem Printed.networkOn_gridProcs_poly (g : ℕ) (tr : Bool) (NM : NetMachine) (hN : NM.PolyTimeSteps) : (networkOn g NM (gridProcs g tr)).PolyTimeSteps := by sorry
