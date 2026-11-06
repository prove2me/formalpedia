-- Prove2me | Theorems.Thm_Sat3Graph_size_dnode_le
-- name    : Sat3Graph.size_dnode_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:40.443382+00:00
-- url     : https://prove2.me/theorems/1ffb2414-411c-4ad8-80f8-e9a5a3c51f4a
-- title:
--   Sat3 Graph: size dnode le
-- statement:
--   The size of a node of the tree for Dominating Set: at most (4w + 12)·(n+2)³.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Dominating.lean#L44-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Dominating.lean#L44-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Ask
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Dominating
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems Paper SizeCircuit SplitSat

theorem Sat3Graph.size_dnode_le {w n s : ℕ} {x : DNode} (hs : s ≤ n) (h1 : x.1 = (List.replicate n (), s)) (h2 : x.2.1.length ≤ n)
    (h3 : ∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) (h4 : x.2.2.length ≤ 2 * n) (h5 : Shaped w n x.2.2) :
    size x ≤ (4 * w + 12) * (n + 2) ^ 3 := by sorry
