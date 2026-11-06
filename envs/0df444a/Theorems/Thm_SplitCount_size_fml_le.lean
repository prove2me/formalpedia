-- Prove2me | Theorems.Thm_SplitCount_size_fml_le
-- name    : SplitCount.size_fml_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:34:00.91733+00:00
-- url     : https://prove2.me/theorems/0fd5f628-12e2-4465-beff-545708a589a8
-- title:
--   Split Count: size fml le
-- statement:
--   A formula of at most m clauses of at most k literals with variables below n has size at most
--   m(k(n+3)+2) + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L51-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L51-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_SatTopK_size_fml_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.size_fml_le {k : ℕ} {x : Fml} {m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) : size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 := by sorry
