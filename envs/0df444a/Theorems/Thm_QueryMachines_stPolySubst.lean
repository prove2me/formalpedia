-- Prove2me | Theorems.Thm_QueryMachines_stPolySubst
-- name    : QueryMachines.stPolySubst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:58:00.998984+00:00
-- url     : https://prove2.me/theorems/4633273b-5951-424b-ab6f-b925b990004d
-- title:
--   Query Machines: st Poly Subst
-- statement:
--   `StPolySubst` holds: queries answered by a machine with query access and polynomial-time steps
--   give a machine with query access and polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Poly.lean#L378-L378
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Poly.lean#L378-L378

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

theorem QueryMachines.stPolySubst : StPolySubst := by sorry
