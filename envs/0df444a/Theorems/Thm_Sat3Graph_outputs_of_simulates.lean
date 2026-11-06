-- Prove2me | Theorems.Thm_Sat3Graph_outputs_of_simulates
-- name    : Sat3Graph.outputs_of_simulates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:53:54.673379+00:00
-- url     : https://prove2.me/theorems/bab92457-8ed4-4155-a316-e08936695699
-- title:
--   Sat3 Graph: outputs of simulates
-- statement:
--   Let M simulate Ms with polynomial overhead. There is C such that: whenever Ms, started on a word
--   x of length at most 2·(n+2)², ends with the bit b within T ≤ c·2^{(δ/2)n} steps on states of size at
--   most c·(n+2)^c, then M, started on x, halts with b within ⌊C·2^{δn}⌋ steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L67-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L67-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Host
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat

theorem Sat3Graph.outputs_of_simulates {M : Turing.TM2ComputableAux Bool Bool} {Ms : StepMachine (List Bool) Bool} {q : ℕ} (hs : Simulates M Ms q)
    {δ : ℝ} (hδ : 0 < δ) (c : ℕ) : ∃ C : ℕ, ∀ (n : ℕ) (x : List Bool) (b : Bool) (T : ℕ), x.length ≤ 2 * (n + 2) ^ 2 →
      Ms.Runs x T (c * (n + 2) ^ c) b → (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n) → Outputs M x [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
