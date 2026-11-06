-- Prove2me | Theorems.Thm_Sat3Graph_numFresh_colorF
-- name    : Sat3Graph.numFresh_colorF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:22.098886+00:00
-- url     : https://prove2.me/theorems/af24eb56-8ad8-4625-af00-6a150e1b74d7
-- title:
--   Sat3 Graph: num Fresh color F
-- statement:
--   The formula of the colorings needs at most (k − 3)·n new variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Coloring.lean#L37-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Coloring.lean#L37-L51

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
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SplitSat

theorem Sat3Graph.numFresh_colorF (k n : ℕ) (m : List Bool) : numFresh (colorF k n m) ≤ (k - 3) * n := by sorry
