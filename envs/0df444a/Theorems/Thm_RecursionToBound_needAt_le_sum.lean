-- Prove2me | Theorems.Thm_RecursionToBound_needAt_le_sum
-- name    : RecursionToBound.needAt_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T07:59:55.966042+00:00
-- url     : https://prove2.me/theorems/8876e3bf-a4ae-4db6-8a82-a14c576c87a6
-- title:
--   Recursion To Bound: need At le sum
-- statement:
--   The exponent for one output with Δ ≤ D is at most the sum of its parts, all but the exponent of
--   the solver taken at D.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L126-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L126-L154

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
import Theorems.Thm_VariableBound_Net_Main_size

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper

theorem RecursionToBound.needAt_le_sum {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (k n : ℕ) {Δ D : ℕ} (h : Δ ≤ D) :
    needAt S k i n Δ ≤ 3 * S.K i ^ 8 * (S.K i).size + PbD (S.K i) n D * (2 * (3 * S.K i ^ 8) / S.K i + 1) +
      (S.K i - 1) * lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n D) (PbD (S.K i) n D) +
      S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ)) (),
        List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n Δ) (BbD k n)) ()) +
      3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n D) +
      (Nat.size (8 * (10 * n + 1) * (sbMax D + 1) * (Nat.size (D * n) + 2) + 8) + 1) := by sorry
