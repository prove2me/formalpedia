-- Prove2me | Theorems.Thm_QueryMachines_stPolyClose
-- name    : QueryMachines.stPolyClose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:58:42.230199+00:00
-- url     : https://prove2.me/theorems/97faf1b9-3830-4bbe-b0d2-dc17ea94db05
-- title:
--   Query Machines: st Poly Close
-- statement:
--   `StPolyClose` holds: a machine with query access and polynomial-time steps, with an oracle built
--   in that is computed in polynomial time from the query, has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Poly.lean#L382-L382
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Poly.lean#L382-L382

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Poly
set_option autoImplicit false
section
section
open QueryMachines
open Groundwork QueryMachine

theorem QueryMachines.stPolyClose : StPolyClose := by sorry
