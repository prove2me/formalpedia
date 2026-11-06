-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_pad_enough
-- name    : SparsificationLemma.Mach.pad_enough
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:13.187574+00:00
-- url     : https://prove2.me/theorems/e9539b2c-e016-4117-b177-466af21f874e
-- title:
--   Mach: pad enough
-- statement:
--   2^(a + k + 3·size N + 9) units suffice for 2^(a+1) nodes, if k, n and m are at most N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L155-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L155-L185

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Len
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo

theorem SparsificationLemma.Mach.pad_enough (a : ℕ) {k n m N : ℕ} (hk : k ≤ N) (hn : n ≤ N) (hm : m ≤ N) :
    2 ^ (a + 1) * (nodeLen k n m + 2) + 6 ≤ 2 ^ (a + k + 3 * Nat.size N + 9) := by sorry
