-- Prove2me | Theorems.Thm_SplitSat_length_le_of_nodup
-- name    : SplitSat.length_le_of_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:45:56.595312+00:00
-- url     : https://prove2.me/theorems/098515c1-5322-4da3-a1cf-285bb2b2e001
-- title:
--   Split Sat: length le of nodup
-- statement:
--   A formula with variables below n, at most k literals per clause and no clause written twice has
--   at most 2^k·(n+2)^k clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L75-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L75-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.length_le_of_nodup {k n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hnd : ψ.Nodup) :
    ψ.length ≤ 2 ^ k * (n + 2) ^ k := by sorry
