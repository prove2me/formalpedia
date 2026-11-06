-- Prove2me | Theorems.Thm_Sat3Graph_decidesGraph_mono
-- name    : Sat3Graph.decidesGraph_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:53:55.097438+00:00
-- url     : https://prove2.me/theorems/8f557cb7-2b2e-499a-a0cf-67347a94481e
-- title:
--   Sat3 Graph: decides Graph mono
-- statement:
--   `DecidesGraph Ms p δ c` stays true when δ and c are made larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L51-L55

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

theorem Sat3Graph.decidesGraph_mono {Ms : StepMachine (List Bool) Bool} {p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop} {δ δ' : ℝ} {c c' : ℕ}
    (hδ : δ ≤ δ') (hc : c ≤ c') (h : DecidesGraph Ms p δ c) : DecidesGraph Ms p δ' c' := by sorry
