-- Prove2me | Theorems.Thm_SplitCount_sparsifiesPlain_of
-- name    : SplitCount.sparsifiesPlain_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:36:17.230476+00:00
-- url     : https://prove2.me/theorems/c61a1a50-3643-430f-bb96-c23ed1239b1b
-- title:
--   Split Count: sparsifies Plain of
-- statement:
--   The bounds of proof/consequences/CountKSat/ on the tree whose root has the clauses xᵢ ∨ ¬xᵢ on
--   its side list hold for the tree whose side list starts empty and whose nodes carry n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L116-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L116-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Tree
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width

theorem SplitCount.sparsifiesPlain_of {k : ℕ} {ε : ℝ} {θ : ℕ → ℕ} {Dd Bl Sk : ℕ} (h : SparsifiesC k ε (stepC θ k) Dd Bl Sk) : SparsifiesPlain k ε (stepC θ k) Dd Bl Sk := by sorry
