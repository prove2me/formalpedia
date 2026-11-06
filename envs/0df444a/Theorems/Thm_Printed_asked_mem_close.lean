-- Prove2me | Theorems.Thm_Printed_asked_mem_close
-- name    : Printed.asked_mem_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:09:49.603403+00:00
-- url     : https://prove2.me/theorems/5675f2cb-0d7e-4bf1-8572-e3e00e20939f
-- title:
--   Printed: asked mem close
-- statement:
--   «Is z ∈ S_a?», asked, with the oracle built in: one step, then the answer is read as yes if it
--   is not 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L55-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingEntry.lean#L55-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.asked_mem_close (O : NetQuery → Option ℤ) :
    (asked.close O).mem = Stepped.mapOut (Stepped.ofOption fun a : NetInput × WQ => O (Sum.inl a.2)) fun v : ℤ => decide (v ≠ 0) := by sorry
