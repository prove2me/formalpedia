-- Prove2me | Theorems.Thm_Sat3Graph_hostedColor_of
-- name    : Sat3Graph.hostedColor_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:28.206004+00:00
-- url     : https://prove2.me/theorems/e2b8aae1-d5d6-488c-bae9-dba7a1b5d837
-- title:
--   Sat3 Graph: hosted Color of
-- statement:
--   The same for k-Coloring.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L126-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L126-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Host
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat

theorem Sat3Graph.hostedColor_of {Ms : StepMachine (List Bool) Bool} {k : ℕ} {δ : ℝ} {c : ℕ} (hδ : 0 < δ) (hp : PolyTimeSteps Ms) (h : DecidesColor Ms k (δ / 2) c) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Simulates M Ms q ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ b : Bool, (b = true ↔ G.Colorable k) ∧ Outputs M (code G) [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
