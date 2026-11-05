-- Prove2me | Theorems.Thm_Suffices_size_node_le
-- name    : Suffices.size_node_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:24:23.508423+00:00
-- url     : https://prove2.me/theorems/fa8d60c9-bdd9-40a2-b303-d9030ca338c4
-- title:
--   Suffices: size node le
-- statement:
--   A node (ψ, 𝒩) within the bounds of `Enumerate.Enumerates.stack` has size at most 142·N².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L51-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L51-L60

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

theorem Suffices.size_node_le {x : CNode} {m n N : ℕ} (h1 : x.1.length ≤ m * 2 ^ 3) (h2 : x.2.length ≤ 2 * n) (h3 : ∀ C ∈ x.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n)
    (h4 : ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) (hm : m ≤ N) (hn : n ≤ N) (hN : 1 ≤ N) : size x ≤ 142 * N ^ 2 := by sorry
