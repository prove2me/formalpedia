-- Prove2me | Theorems.Thm_Suffices_loop_bound
-- name    : Suffices.loop_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:26:08.90129+00:00
-- url     : https://prove2.me/theorems/760ae5d3-4d23-44b4-b3a8-40f67fc991d8
-- title:
--   Suffices: loop bound
-- statement:
--   The bound on the stack, plus 4, is at most c·N^c for c = 143·(D + 1) + 5.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L76-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L76-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits

theorem Suffices.loop_bound (D N : ℕ) (hN : 1 ≤ N) : (143 * (D + 1) + 1) * N ^ 3 + 4 ≤ (143 * (D + 1) + 5) * N ^ (143 * (D + 1) + 5) := by sorry
