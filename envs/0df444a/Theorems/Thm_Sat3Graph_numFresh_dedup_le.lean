-- Prove2me | Theorems.Thm_Sat3Graph_numFresh_dedup_le
-- name    : Sat3Graph.numFresh_dedup_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:52:08.10567+00:00
-- url     : https://prove2.me/theorems/d7ba63d0-8fed-4ca8-8f68-68f6f87fc858
-- title:
--   Sat3 Graph: num Fresh dedup le
-- statement:
--   Striking out repeated clauses does not make the number of new variables larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L58-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L58-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
import Theorems.Thm_Groundwork_PolyT_dedup
attribute [local fun_prop] Groundwork.PolyT.dedup


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width

theorem Sat3Graph.numFresh_dedup_le : ∀ x : Fml, numFresh x.dedup ≤ numFresh x
  := by sorry
