-- Prove2me | Theorems.Thm_Printed_size_units
-- name    : Printed.size_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:08:53.868789+00:00
-- url     : https://prove2.me/theorems/7e7100ab-f104-4bfc-bab2-66057c9f29a9
-- title:
--   Printed: size units
-- statement:
--   A list of units of length n has size 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L34-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L34-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
import Definitions.Def_Printed_LevelCost
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

theorem Printed.size_units (l : List Unit) : size l = 2 * l.length + 1 := by sorry
