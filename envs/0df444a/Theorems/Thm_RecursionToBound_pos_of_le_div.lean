-- Prove2me | Theorems.Thm_RecursionToBound_pos_of_le_div
-- name    : RecursionToBound.pos_of_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:25:14.896106+00:00
-- url     : https://prove2.me/theorems/d58e745a-480d-4b87-bfe0-5e73031b3b16
-- title:
--   Recursion To Bound: pos of le div
-- statement:
--   A fraction a/b that is at least e > 0 has a > 0 and b > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L62-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L62-L72

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

theorem RecursionToBound.pos_of_le_div {r : ℕ × ℕ} {e : ℝ} (he : 0 < e) (h : e ≤ (r.1 : ℝ) / r.2) : 0 < r.1 ∧ 0 < r.2 := by sorry
