-- Prove2me | Theorems.Thm_Suffices_size_clauses_le
-- name    : Suffices.size_clauses_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:26:22.415875+00:00
-- url     : https://prove2.me/theorems/26b5aeeb-19c2-4271-b446-99af518633a3
-- title:
--   Suffices: size clauses le
-- statement:
--   A formula of at most m clauses of at most 3 literals on variables below n ≤ N has size at most
--   14·m·N + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L44-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L44-L48

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

theorem Suffices.size_clauses_le {x : Fml} {m k n N : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hk : k ≤ 3) (hn : n ≤ N) (hN : 1 ≤ N) : size x ≤ m * (14 * N) + 1 := by sorry
