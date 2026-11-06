-- Prove2me | Theorems.Thm_Printed_tableQ_poly
-- name    : Printed.tableQ_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:42:29.533468+00:00
-- url     : https://prove2.me/theorems/975fa4ee-540f-4330-95ec-17227310bebf
-- title:
--   Printed: table Q poly
-- statement:
--   One entry W̃_γ(Θ) has polynomial-time steps, if the four procedures have and P_a, c_{a,b} are
--   given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L64-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L64-L82

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

theorem Printed.tableQ_poly {Q A C : Type} [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (K g : ℕ) (Np : ProcsQ Q A C) (h : Np.under.toPaperNetwork.Keeps)
    [IsPolyQ Np.mem] [IsPolyQ Np.W] [IsPolyQ Np.Ψ] [IsPolyQ Np.f] : (tableQ K g Np).PolyTimeSteps := by sorry
