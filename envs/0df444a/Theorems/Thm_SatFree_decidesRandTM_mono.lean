-- Prove2me | Theorems.Thm_SatFree_decidesRandTM_mono
-- name    : SatFree.decidesRandTM_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:48:29.644486+00:00
-- url     : https://prove2.me/theorems/2aae2145-c1f2-4184-935e-c57c2538a231
-- title:
--   Sat Free: decides Rand TM mono
-- statement:
--   An algorithm with error at most p has error at most p', if p ≤ p'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Random.lean#L57-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Random.lean#L57-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random
set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal

theorem SatFree.decidesRandTM_mono {p p' : ℝ} (hp : p ≤ p') {k : ℕ} {M : TM2ComputableAux Bool Bool} {r t : ℕ → ℕ} (h : DecidesRandTM p k M r t) :
    DecidesRandTM p' k M r t := by sorry
