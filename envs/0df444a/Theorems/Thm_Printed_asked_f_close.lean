-- Prove2me | Theorems.Thm_Printed_asked_f_close
-- name    : Printed.asked_f_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:09:58.888549+00:00
-- url     : https://prove2.me/theorems/142ec54a-2e8e-41fd-804b-7ddae2481634
-- title:
--   Printed: asked f close
-- statement:
--   f_{a,b}(z, θ), asked, with the oracle built in: one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L67-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L67-L67

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

theorem Printed.asked_f_close (O : NetQuery → Option ℤ) : (asked.close O).f = Stepped.ofOption fun a : NetInput × FQ => O (Sum.inr (Sum.inr (Sum.inr a.2))) := by sorry
