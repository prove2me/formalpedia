-- Prove2me | Theorems.Thm_Sat3Graph_withGamma_replicate
-- name    : Sat3Graph.withGamma_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:36.071696+00:00
-- url     : https://prove2.me/theorems/42d55037-5379-4425-8cfb-56b0077fd5d3
-- title:
--   Sat3 Graph: with Gamma replicate
-- statement:
--   What `withGamma` hands over on (n in unary, s, ψ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Ask.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Ask.lean#L35-L37

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
import Theorems.Thm_Groundwork_PolyT_dedup
attribute [local fun_prop] Groundwork.PolyT.dedup


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit SplitSat

theorem Sat3Graph.withGamma_replicate (gates : ℕ → ℕ → List CircuitLowerBound.GateD) (n s : ℕ) (ψ : Fml) :
    withGamma gates (List.replicate n (), s, ψ) = (List.replicate (numVars gates n s) (), (ψ ++ gamma gates n s).dedup) := by sorry
