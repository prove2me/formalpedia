-- Prove2me | Theorems.Thm_Printed_asked_keepsP
-- name    : Printed.asked_keepsP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:42:12.550199+00:00
-- url     : https://prove2.me/theorems/ec9a2c31-237f-4329-9736-fa3224cd84a7
-- title:
--   Printed: asked keeps P
-- statement:
--   The numbers of Definition 2(iii) stand in the input in unary, and the step machines under the
--   four procedures have polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L47-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingPoly.lean#L47-L60

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

theorem Printed.asked_keepsP : KeepsP asked.under := by sorry
