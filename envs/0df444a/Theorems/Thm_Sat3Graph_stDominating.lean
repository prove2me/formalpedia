-- Prove2me | Theorems.Thm_Sat3Graph_stDominating
-- name    : Sat3Graph.stDominating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:19.189645+00:00
-- url     : https://prove2.me/theorems/3a2322a0-8d6b-4610-bafb-1af93cdfbe5b
-- title:
--   Sat3 Graph: st Dominating
-- statement:
--   **`StDominating`.** Let the tree for w have at most 2^{δn/2} leaves
--   (`GraphProblems.ShortensD w (δ/2)`) and let D decide 3-SAT with an exponent δ₃ ≥ 0 such that δ₃·(a +
--   1 + 3·(w − 3)) ≤ δ/2. Then `DOM w gates D` decides Dominating Set within c'·2^{δn} steps, on states
--   of size at most c'·(n+2)^{c'}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Dominating.lean#L75-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Dominating.lean#L75-L162

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
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems Paper SizeCircuit SplitSat

theorem Sat3Graph.stDominating : StDominating := by sorry
