-- Prove2me | Theorems.Thm_Suffices_size_sparse_le
-- name    : Suffices.size_sparse_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:26:30.421759+00:00
-- url     : https://prove2.me/theorems/8ec4e0ef-fb08-4100-9264-72485ad72ed0
-- title:
--   Suffices: size sparse le
-- statement:
--   A formula of at most M·n clauses, together with n, has size at most (14·M + 2)·N².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L94-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L94-L99

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

theorem Suffices.size_sparse_le {Φ : Fml} {M n N : ℕ} (hm : Φ.length ≤ M * n) (hx : ∀ C ∈ Φ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) (hn : n ≤ N) (hN : 1 ≤ N) : size Φ + n ≤ (14 * M + 2) * N ^ 2 := by sorry
