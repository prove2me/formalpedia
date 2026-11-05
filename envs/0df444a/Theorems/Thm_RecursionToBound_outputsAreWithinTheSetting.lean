-- Prove2me | Theorems.Thm_RecursionToBound_outputsAreWithinTheSetting
-- name    : RecursionToBound.outputsAreWithinTheSetting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:38:21.444193+00:00
-- url     : https://prove2.me/theorems/8bb8f51e-dfa7-4f3a-8f6d-fbff7bfc3094
-- title:
--   Recursion To Bound: outputs Are Within The Setting
-- statement:
--   «… so log Δ ≤ 3k·log(8k/e) + 2 = O(k·log(k/e)). As e ≥ (log n)^(−C₀) and k ≤ (log n)^(1/4), this
--   is at most 3k(3 + (C₀ + 1/4)·log log n) + 2, which is at most 4kC₀·log log n for large n, because C₀
--   ≥ 1» (Step 5 of Appendix D), for every Δ from 2 to the bound on the occurrences; with Δ ≤ n + 1 and
--   n ≥ 29·⌈log₂(2Δ)⌉ + 19.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L222-L286
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Numbers.lean#L222-L286

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

theorem RecursionToBound.outputsAreWithinTheSetting : OutputsAreWithinTheSetting := by sorry
