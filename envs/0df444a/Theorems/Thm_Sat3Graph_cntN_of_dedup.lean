-- Prove2me | Theorems.Thm_Sat3Graph_cntN_of_dedup
-- name    : Sat3Graph.cntN_of_dedup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:51:14.630261+00:00
-- url     : https://prove2.me/theorems/b39e4592-1cef-45f3-a2d4-7fdc64cd25c3
-- title:
--   Sat3 Graph: cnt N of dedup
-- statement:
--   Striking out repeated clauses does not change the number of satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L82-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L82-L84

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

theorem Sat3Graph.cntN_of_dedup (N : ℕ) (ψ : Fml) : cntN N ψ.dedup = cntN N ψ := by sorry
