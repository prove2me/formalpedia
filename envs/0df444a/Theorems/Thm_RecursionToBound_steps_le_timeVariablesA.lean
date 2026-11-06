-- Prove2me | Theorems.Thm_RecursionToBound_steps_le_timeVariablesA
-- name    : RecursionToBound.steps_le_timeVariablesA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:04.735525+00:00
-- url     : https://prove2.me/theorems/58f38bd5-903a-4b77-abd5-7d140f4380b9
-- title:
--   Recursion To Bound: steps le time Variables A
-- statement:
--   The running time q·(len + 2^E + 1)^q of a machine that is given a padding string of 2^E units,
--   against the bound of Theorem D (a). If 1 ≤ a·X, E ≤ a·X and k·log n ≤ a·X for X = k²·e·n·log(k/e), n
--   ≥ 4 and len + 1 ≤ (n+2)^(5k), then q·(len + 2^E + 1)^q ≤ 2^{12qa·X}, rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/End.lean#L61-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/End.lean#L61-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_Exponent
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RecursionToBound_End
set_option autoImplicit false
section
section
open RecursionToBound
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End UniformInK Wrap MainTheoremForms PairsToBound VariableBound.Paper
open Sat3 (CNF)

theorem RecursionToBound.steps_le_timeVariablesA (q a : ℕ) {k n E len : ℕ} {e : ℝ} (h1 : 1 ≤ (a : ℝ) * expVariablesA k n e) (hE : (E : ℝ) ≤ (a : ℝ) * expVariablesA k n e)
    (hk : (k : ℝ) * lg n ≤ (a : ℝ) * expVariablesA k n e) (hn : 4 ≤ n) (hlen : len + 1 ≤ (n + 2) ^ (5 * k)) :
    q * (len + 2 ^ E + 1) ^ q ≤ timeVariablesA (q * 12 * a) k n e := by sorry
