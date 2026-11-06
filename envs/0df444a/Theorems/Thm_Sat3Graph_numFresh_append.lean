-- Prove2me | Theorems.Thm_Sat3Graph_numFresh_append
-- name    : Sat3Graph.numFresh_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:58:50.654543+00:00
-- url     : https://prove2.me/theorems/48605ffe-2573-462e-976a-08eb4b22c7b0
-- title:
--   Sat3 Graph: num Fresh append
-- statement:
--   The numbers of new variables of two formulas add up.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L49-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L49-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width

theorem Sat3Graph.numFresh_append (x y : Fml) : numFresh (x ++ y) = numFresh x + numFresh y := by sorry
