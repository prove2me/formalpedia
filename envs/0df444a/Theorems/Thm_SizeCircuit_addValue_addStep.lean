-- Prove2me | Theorems.Thm_SizeCircuit_addValue_addStep
-- name    : SizeCircuit.addValue_addStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:03.69511+00:00
-- url     : https://prove2.me/theorems/21b8f7d3-be42-4969-ab7a-dace71b2594e
-- title:
--   Size Circuit: add Value add Step
-- statement:
--   If v obeys the gates after a step, it obeys the gates before it, and the step has kept the
--   value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L232-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L232-L252

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.addValue_addStep (v : ℕ → Bool) (n : ℕ) (st : AddState) (h : Obeys v n (addStep n st).2.2.2) :
    Obeys v n st.2.2.2 ∧ addValue v (addStep n st) = addValue v st := by sorry
