-- Prove2me | Theorems.Thm_Sat3Graph_numFresh_append_le
-- name    : Sat3Graph.numFresh_append_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:16.653789+00:00
-- url     : https://prove2.me/theorems/0450e0ab-8dbf-4af8-9252-7de5886ac617
-- title:
--   Sat3 Graph: num Fresh append le
-- statement:
--   Clauses of at most 3 literals written behind a formula need no new variable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Coloring.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Coloring.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Split
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Coloring
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SplitSat

theorem Sat3Graph.numFresh_append_le {x y : Fml} {m : ℕ} (hx : numFresh x ≤ m) (hy : ∀ C ∈ y, C.length ≤ 3) : numFresh (x ++ y) ≤ m := by sorry
