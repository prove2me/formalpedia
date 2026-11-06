-- Prove2me | Theorems.Thm_SizeCircuit_ext_of_le
-- name    : SizeCircuit.ext_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:01.177138+00:00
-- url     : https://prove2.me/theorems/72c0ba24-9df7-4fd1-9644-5845988afb26
-- title:
--   Size Circuit: ext of le
-- statement:
--   From N on, the assignment b on N variables, read on all numbers, is 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L155-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L155-L155

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
import Theorems.Thm_CountKSat_Value_ext_of_le

set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.ext_of_le {N : ℕ} (b : Fin N → Bool) {i : ℕ} (h : N ≤ i) : ext b i = false := by sorry
