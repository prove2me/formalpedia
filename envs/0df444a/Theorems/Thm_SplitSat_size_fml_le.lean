-- Prove2me | Theorems.Thm_SplitSat_size_fml_le
-- name    : SplitSat.size_fml_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:46:31.465921+00:00
-- url     : https://prove2.me/theorems/ec113beb-c258-4e84-baec-d0550384be18
-- title:
--   Split Sat: size fml le
-- statement:
--   A bound on the size of a formula of at most m clauses of at most k literals with variables below
--   n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L110-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L110-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_SatTopK_size_fml_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.size_fml_le {k : ℕ} {x : Fml} {m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 := by sorry
