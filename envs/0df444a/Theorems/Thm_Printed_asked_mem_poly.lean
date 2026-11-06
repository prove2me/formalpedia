-- Prove2me | Theorems.Thm_Printed_asked_mem_poly
-- name    : Printed.asked_mem_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:41:50.267196+00:00
-- url     : https://prove2.me/theorems/c34fed3e-d9bf-44e8-942b-b9fed2878715
-- title:
--   Printed: asked mem poly
-- statement:
--   «Is z ∈ S_a?», asked.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_Exits_Poly
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingPoly
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem

set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.asked_mem_poly : asked.mem.PolyTimeSteps := by sorry
