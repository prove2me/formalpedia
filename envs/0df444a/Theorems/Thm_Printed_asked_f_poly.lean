-- Prove2me | Theorems.Thm_Printed_asked_f_poly
-- name    : Printed.asked_f_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:42:00.397787+00:00
-- url     : https://prove2.me/theorems/b0717892-4664-4cb6-a8b5-174f0fce4781
-- title:
--   Printed: asked f poly
-- statement:
--   f_{a,b}(z, θ), asked.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L43-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L43-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_Exits_Poly
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingPoly
set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.asked_f_poly : asked.f.PolyTimeSteps := by sorry
