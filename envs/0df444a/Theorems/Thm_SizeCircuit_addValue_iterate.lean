-- Prove2me | Theorems.Thm_SizeCircuit_addValue_iterate
-- name    : SizeCircuit.addValue_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:19.146174+00:00
-- url     : https://prove2.me/theorems/abceaac4-5c81-4a22-ad6e-dfb7f1f1ac0f
-- title:
--   Size Circuit: add Value iterate
-- statement:
--   If v obeys the gates after k steps, the value is still the number of inputs that are 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L255-L266
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L255-L266

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

theorem SizeCircuit.addValue_iterate (v : ℕ → Bool) (n : ℕ) : ∀ k : ℕ, Obeys v n ((addStep n)^[k] (addStart n)).2.2.2 →
    addValue v ((addStep n)^[k] (addStart n)) = onesAmong v (List.range n) := by sorry
