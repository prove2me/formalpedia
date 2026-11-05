-- Prove2me | Theorems.Thm_Suffices_size_stack_le
-- name    : Suffices.size_stack_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:32:45.700661+00:00
-- url     : https://prove2.me/theorems/562e7368-39bc-4557-a4d0-473855881689
-- title:
--   Suffices: size stack le
-- statement:
--   A stack of at most D·n + 1 such nodes has size at most (143·(D + 1) + 1)·N³.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L63-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L63-L73

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits

theorem Suffices.size_stack_le {st : List CNode} {D n N : ℕ} (hl : st.length ≤ D * n + 1) (hx : ∀ x ∈ st, size x ≤ 142 * N ^ 2) (hn : n ≤ N) (hN : 1 ≤ N) : size st ≤ (143 * (D + 1) + 1) * N ^ 3 := by sorry
