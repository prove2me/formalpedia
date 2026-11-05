-- Prove2me | Theorems.Thm_RecursionToBound_eps_between
-- name    : RecursionToBound.eps_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:25:58.99372+00:00
-- url     : https://prove2.me/theorems/f70730f4-87e1-4ee5-8f82-fd717a72a17c
-- title:
--   Recursion To Bound: eps between
-- statement:
--   «Take ε ≤ 1 between e and 2e»: if e ≤ a/b ≤ 2e and e ≤ 1, then e ≤ ε ≤ 2e and ε ≤ 1 for ε =
--   min(a/b, 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L76-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L76-L79

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

theorem RecursionToBound.eps_between {r : ℕ × ℕ} {e : ℝ} (he1 : e ≤ 1) (h1 : e ≤ (r.1 : ℝ) / r.2) (h2 : (r.1 : ℝ) / r.2 ≤ 2 * e) :
    e ≤ ((epsOf r : ℚ) : ℝ) ∧ ((epsOf r : ℚ) : ℝ) ≤ 2 * e ∧ ((epsOf r : ℚ) : ℝ) ≤ 1 := by sorry
