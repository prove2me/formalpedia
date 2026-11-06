-- Prove2me | Theorems.Thm_VariableBound_Count_sq_le
-- name    : VariableBound.Count.sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:49:35.946349+00:00
-- url     : https://prove2.me/theorems/215eeaa8-1968-4e6b-bc61-2a56a57faa6c
-- title:
--   Count: sq le
-- statement:
--   (2Δ)² ≤ 2^n, if 2·⌈log₂(2Δ)⌉ ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L77-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Count/Correct.lean#L77-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset

theorem VariableBound.Count.sq_le (n Δ : ℕ) (h : 2 * LD Δ ≤ n) : (2 * Δ) ^ 2 ≤ 2 ^ n := by sorry
