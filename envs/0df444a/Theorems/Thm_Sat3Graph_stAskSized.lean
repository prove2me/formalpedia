-- Prove2me | Theorems.Thm_Sat3Graph_stAskSized
-- name    : Sat3Graph.stAskSized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:55:32.982715+00:00
-- url     : https://prove2.me/theorems/8779e8a0-ae79-423d-9a5c-263b7d72a8c3
-- title:
--   Sat3 Graph: st Ask Sized
-- statement:
--   **`StAskSized`.** Let gates test the size with at most a·(n+1) gates, and let D decide 3-SAT
--   with an exponent δ₃ ≥ 0 such that δ₃·(a + 1 + B) ≤ δ. On (n in unary, s, ψ), for s ≤ n and ψ of
--   width at most w on x₀ … xₙ₋₁ with (w − 3)·|ψ| ≤ B·(n+1), `askSized gates D` says, within c'·2^{δn}
--   steps and on states of size at most c'·(n+2)^{c'}, whether ψ has a satisfying assignment with
--   exactly s true variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Ask.lean#L44-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Ask.lean#L44-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Split
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_Gamma
import Definitions.Def_SizeCircuit_Sized
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Ask
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit SplitSat

theorem Sat3Graph.stAskSized : StAskSized := by sorry
