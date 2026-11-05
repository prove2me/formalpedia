-- Prove2me | Theorems.Thm_Suffices_size_input_le
-- name    : Suffices.size_input_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:26:18.812424+00:00
-- url     : https://prove2.me/theorems/2f6cdc51-81e5-4825-b4bc-1c39f815f178
-- title:
--   Suffices: size input le
-- statement:
--   The input as it is held after decoding, (1ⁿ, ψ) with at most N clauses, has size at most 18·N².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L84-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L84-L91

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

theorem Suffices.size_input_le {ψ : Fml} {n N : ℕ} (hm : ψ.length ≤ N) (hx : ∀ C ∈ ψ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) (hn : n ≤ N) (hN : 1 ≤ N) : size (List.replicate n (), ψ) ≤ 18 * N ^ 2 := by sorry
