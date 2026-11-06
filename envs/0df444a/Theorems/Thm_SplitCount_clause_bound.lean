-- Prove2me | Theorems.Thm_SplitCount_clause_bound
-- name    : SplitCount.clause_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:46:52.461182+00:00
-- url     : https://prove2.me/theorems/e65f3278-ece0-4a89-a391-b69c52a41603
-- title:
--   Split Count: clause bound
-- statement:
--   A clause of at most w literals on variables below n ≤ M: the bound of `size_fml_le` for one
--   clause is at most (4w + 2)·M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L109-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L109-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Leaf
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ

theorem SplitCount.clause_bound {w n M : ℕ} (hn : n ≤ M) (h1 : 1 ≤ M) : w * (n + 2 + 1) + 1 + 1 ≤ (4 * w + 2) * M := by sorry
