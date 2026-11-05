-- Prove2me | Theorems.Thm_RecursionToBound_lg_le_of_le_pow
-- name    : RecursionToBound.lg_le_of_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:27.47871+00:00
-- url     : https://prove2.me/theorems/c318a081-d7f4-45b3-ba62-140043dfbfff
-- title:
--   Recursion To Bound: lg le of le pow
-- statement:
--   If Δ ≤ 2·a^j + 2 with a ≥ 1, then log Δ ≤ j·log a + 2, for Δ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L181-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L181-L189

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Params_Ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_Numbers
set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper

theorem RecursionToBound.lg_le_of_le_pow {Δ j : ℕ} {a : ℝ} (hΔ : 1 ≤ Δ) (ha : 1 ≤ a) (h : (Δ : ℝ) ≤ 2 * a ^ j + 2) : lg Δ ≤ j * lg a + 2 := by sorry
