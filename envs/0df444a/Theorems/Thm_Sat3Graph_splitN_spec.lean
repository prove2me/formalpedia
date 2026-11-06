-- Prove2me | Theorems.Thm_Sat3Graph_splitN_spec
-- name    : Sat3Graph.splitN_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:51:46.542136+00:00
-- url     : https://prove2.me/theorems/2c26d575-3470-433b-a243-39b518f254df
-- title:
--   Sat3 Graph: split N spec
-- statement:
--   For a formula x with variables below n: the formula with its long clauses split has at most 3
--   literals per clause, variables below n + (number of new variables), no clause twice, and is
--   satisfiable exactly if x is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L38-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean#L38-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width

theorem Sat3Graph.splitN_spec {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) :
    (∀ C ∈ splitN n x, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n + numFresh x) ∧ (splitN n x).Nodup ∧ ((splitN n x).Sat ↔ x.Sat) := by sorry
