-- Prove2me | Theorems.Thm_Sat3Graph_sat_iff_cntN
-- name    : Sat3Graph.sat_iff_cntN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:53:45.603283+00:00
-- url     : https://prove2.me/theorems/0f0a84db-4d9e-4324-8225-360deab38238
-- title:
--   Sat3 Graph: sat iff cnt N
-- statement:
--   A formula with variables below N is satisfiable exactly if its number of satisfying assignments
--   on N variables is not 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L70-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L70-L79

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

theorem Sat3Graph.sat_iff_cntN {N : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < N) : x.Sat ↔ cntN N x ≠ 0 := by sorry
