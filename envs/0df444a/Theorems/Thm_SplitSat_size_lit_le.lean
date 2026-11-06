-- Prove2me | Theorems.Thm_SplitSat_size_lit_le
-- name    : SplitSat.size_lit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:25.215344+00:00
-- url     : https://prove2.me/theorems/fb28e6da-6dfa-4509-b542-68ac63c6ed9d
-- title:
--   Split Sat: size lit le
-- statement:
--   A literal on a variable below n has size at most n + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L103-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L103-L106

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_Prog_size_lit_le

set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.size_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : size l ≤ n + 2 := by sorry
