-- Prove2me | Theorems.Thm_Printed_toLists_polyT
-- name    : Printed.toLists_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:42:17.535104+00:00
-- url     : https://prove2.me/theorems/fc89b4da-81e7-4014-9e21-1864388bf4a5
-- title:
--   Printed: to Lists poly T
-- statement:
--   Cutting a setting z_w into its K − 1 strings of λ bits is computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L98-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L98-L100

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

theorem Printed.toLists_polyT {C : Type} [Enc C] (K : ℕ) {lam : C → ℕ} (h : PolyT lam) : PolyT fun y : C × TableQuery => (y.1, toLists K (lam y.1) y.2) := by sorry
