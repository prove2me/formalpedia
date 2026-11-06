-- Prove2me | Theorems.Thm_SizeCircuit_count_ofFn
-- name    : SizeCircuit.count_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:16.209725+00:00
-- url     : https://prove2.me/theorems/807109da-3dd5-442b-9947-ce9dce6348af
-- title:
--   Size Circuit: count of Fn
-- statement:
--   The number of ones of the word of x is the number of places where x is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L102-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L102-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.count_ofFn : ∀ {n : ℕ} (x : Fin n → Bool), (List.ofFn x).count true = (Finset.univ.filter fun i => x i = true).card
  := by sorry
