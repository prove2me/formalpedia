-- Prove2me | Theorems.Thm_SizeCircuit_num_eq_iff
-- name    : SizeCircuit.num_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:54.645363+00:00
-- url     : https://prove2.me/theorems/53dfa631-ed85-4b78-8fe0-d58ace1f6643
-- title:
--   Size Circuit: num eq iff
-- statement:
--   The digits b 0, …, b (L − 1) write s exactly if s has at most L digits and these are its digits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L35-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L35-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.num_eq_iff (b : ℕ → Bool) (L s : ℕ) : num b L = s ↔ s < 2 ^ L ∧ ∀ i < L, b i = s.testBit i := by sorry
