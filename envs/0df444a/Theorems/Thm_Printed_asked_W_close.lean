-- Prove2me | Theorems.Thm_Printed_asked_W_close
-- name    : Printed.asked_W_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:09:13.503104+00:00
-- url     : https://prove2.me/theorems/d50b5639-1656-4993-9467-026819e47481
-- title:
--   Printed: asked W close
-- statement:
--   W_a(z), asked, with the oracle built in: one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L61-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L61-L61

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

theorem Printed.asked_W_close (O : NetQuery → Option ℤ) : (asked.close O).W = Stepped.ofOption fun a : NetInput × WQ => O (Sum.inr (Sum.inl a.2)) := by sorry
