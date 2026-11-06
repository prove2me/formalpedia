-- Prove2me | Theorems.Thm_SizeCircuit_testsSize_sizeGates
-- name    : SizeCircuit.testsSize_sizeGates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:54:06.401193+00:00
-- url     : https://prove2.me/theorems/95cebccc-b5da-45ed-b461-7bfff5c1d7e3
-- title:
--   Size Circuit: tests Size size Gates
-- statement:
--   **«a circuit with O(n) gates of two inputs tests whether |S| = s».** For all n ≥ 1 and all s,
--   `sizeGates n s` has at least one and at most 6·(n+1) gates, every gate reads earlier wires only, and
--   on a word of length n the output is 1 exactly if the word has s ones.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Circuit.lean#L51-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Circuit.lean#L51-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_General
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_SizeCircuit_Compare
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Circuit
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.testsSize_sizeGates : TestsSize sizeGates 6 := by sorry
