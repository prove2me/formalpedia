-- Prove2me | Theorems.Thm_RecursionToBound_six_test
-- name    : RecursionToBound.six_test
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:31.704426+00:00
-- url     : https://prove2.me/theorems/2c1b870c-b45d-415d-9be2-fcabd5bd651e
-- title:
--   Recursion To Bound: six test
-- statement:
--   If (520200·C₀⁴)² ≤ ℓ and k⁴ ≤ ℓ, then 2·(102·C₀·(4kC₀+1))² ≤ ℓ, for C₀, k ≥ 1, because the left
--   side is at most 520200·C₀⁴·k² ≤ ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L246-L256
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L246-L256

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_StepCost
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_OneOutput
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper

theorem RecursionToBound.six_test {C₀ k ℓ : ℕ} (hC : 1 ≤ C₀) (hk : 1 ≤ k) (h1 : (520200 * C₀ ^ 4) ^ 2 ≤ ℓ) (h2 : k ^ 4 ≤ ℓ) : 2 * (102 * C₀ * (4 * k * C₀ + 1)) ^ 2 ≤ ℓ := by sorry
