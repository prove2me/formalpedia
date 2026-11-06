-- Prove2me | Theorems.Thm_Sat3Graph_hostedFor_of
-- name    : Sat3Graph.hostedFor_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:43:04.452954+00:00
-- url     : https://prove2.me/theorems/e6190fd0-1ab6-40ec-87cf-c0cd7b0e6261
-- title:
--   Sat3 Graph: hosted For of
-- statement:
--   A decider for a property of (G, s) with polynomial-time steps and the exponent δ/2 is simulated
--   with polynomial overhead by a Turing machine with finite alphabets that decides the property within
--   ⌊C·2^{δn}⌋ steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L114-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L114-L123

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

theorem Sat3Graph.hostedFor_of {Ms : StepMachine (List Bool) Bool} {p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop} {δ : ℝ} {c : ℕ} (hδ : 0 < δ)
    (hp : PolyTimeSteps Ms) (h : DecidesGraph Ms p (δ / 2) c) : HostedFor Ms p δ := by sorry
