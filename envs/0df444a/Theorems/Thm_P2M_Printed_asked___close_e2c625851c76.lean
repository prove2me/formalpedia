-- Prove2me | Theorems.Thm_P2M_Printed_asked___close_e2c625851c76
-- name    : P2M_Printed_asked___close_e2c625851c76
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:09:55.562207+00:00
-- url     : https://prove2.me/theorems/e94404e8-eef5-4e3b-9b9c-da28930dc1ac
-- title:
--   P2 M Printed asked   close e2c625851c76: P2 M Printed asked   close e2c625851c76
-- statement:
--   Ψ_{a,b}(z, z'), asked, with the oracle built in: one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L64-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L64-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem P2M_Printed_asked___close_e2c625851c76 (O : NetQuery → Option ℤ) : (asked.close O).Ψ = Stepped.ofOption fun a : NetInput × PsiQ => O (Sum.inr (Sum.inr (Sum.inl a.2))) := by sorry

alias «Printed».«asked_Ψ_close» := P2M_Printed_asked___close_e2c625851c76
