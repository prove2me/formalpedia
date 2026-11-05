-- Prove2me | Theorems.Thm_RecursionToBound_LD_le_lg
-- name    : RecursionToBound.LD_le_lg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:12:06.098655+00:00
-- url     : https://prove2.me/theorems/c271921e-2584-415a-9272-06791c1a57b4
-- title:
--   Recursion To Bound: LD le lg
-- statement:
--   ⌈log₂(2Δ)⌉ ≤ log n + 2 for Δ ≤ n, n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L199-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L199-L214

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

theorem RecursionToBound.LD_le_lg {Δ n : ℕ} (hn : 1 ≤ n) (h : Δ ≤ n) : (LD Δ : ℝ) ≤ lg n + 2 := by sorry
