-- Prove2me | Theorems.Thm_SizeCircuit_counts_addStep
-- name    : SizeCircuit.counts_addStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:17.676194+00:00
-- url     : https://prove2.me/theorems/610fd66e-d92d-493c-b0ec-6e6bfba479d2
-- title:
--   Size Circuit: counts add Step
-- statement:
--   While a wire waits, a step lowers the number of waiting wires by exactly one; it writes at most
--   5 gates and finds at most one digit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L158-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L158-L177

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.counts_addStep (n : ℕ) (st : AddState) (h5 : st.1 = [] → st.2.1 = []) (hp : 0 < st.1.length + st.2.1.length) :
    (addStep n st).1.length + (addStep n st).2.1.length + 1 = st.1.length + st.2.1.length ∧
      (addStep n st).2.2.2.length ≤ st.2.2.2.length + 5 ∧ (addStep n st).2.2.1.length ≤ st.2.2.1.length + 1 := by sorry
