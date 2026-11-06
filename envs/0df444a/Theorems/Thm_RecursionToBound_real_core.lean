-- Prove2me | Theorems.Thm_RecursionToBound_real_core
-- name    : RecursionToBound.real_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:29.375778+00:00
-- url     : https://prove2.me/theorems/2449af15-bd2a-45db-9e98-c6043ca6f0a6
-- title:
--   Recursion To Bound: real core
-- statement:
--   The estimate of the exponent, between real numbers: the parts T1, T2, T3, R1, Rx of lower order
--   and the exponent nd of the solver; M is the main part of the bound on the total.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L57-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L57-L101

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

theorem RecursionToBound.real_core {Kr e n W A C₀ M T1 T2 T3 R1 Rx gP U36 Ubr Lc Lg lam nd c1 c2 c3 c4 c5 c7 c8 c9 : ℝ}
    (hKr : 0 < Kr) (he0 : 0 < e) (he1 : e ≤ 1) (hn0 : 0 ≤ n) (hC0 : 0 ≤ C₀) (hgP0 : 0 ≤ gP) (hU36 : 0 ≤ U36)
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (h5 : 0 ≤ c5) (h7 : 0 ≤ c7) (h8 : 0 ≤ c8) (h9 : 0 ≤ c9) (hM : W ≤ A * Kr * e)
    (r1 : Kr * T1 ≤ c1 * (W * n)) (r2 : Kr * T2 ≤ c2 * (W * n)) (r3 : Kr * T3 ≤ c3 * (W * n)) (r4 : gP ≤ c4 * (W * n))
    (r5 : Kr * U36 ≤ c5 * (W * n)) (r6 : Kr * Kr ^ 2 ≤ W * n) (r7 : Kr * (C₀ * Kr ^ 2 * Lc) ≤ c7 * (W * n)) (r8 : Kr * R1 ≤ c8 * (W * n))
    (r9 : Kr * Rx ≤ c9 * (W * n)) (rU : Ubr ≤ M + U36) (rL : lam * Kr ^ 3 ≤ Kr ^ 3 + Kr * Ubr + gP)
    (hr : nd ≤ e * Kr ^ 2 * lam + C₀ * Kr ^ 2 * Lg) (hlog : Lg ≤ Lc) :
    T1 + T2 + T3 + nd + R1 + Rx ≤ e * M + (c1 + c2 + c3 + c4 + c5 + 1 + c7 + c8 + c9) * A * (n * e) := by sorry
