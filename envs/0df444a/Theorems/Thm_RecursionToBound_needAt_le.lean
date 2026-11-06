-- Prove2me | Theorems.Thm_RecursionToBound_needAt_le
-- name    : RecursionToBound.needAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:00:10.659761+00:00
-- url     : https://prove2.me/theorems/b998beda-18d4-4b8c-b0c0-e52053c04335
-- title:
--   Recursion To Bound: need At le
-- statement:
--   Step 4 for one output. Let 2 ≤ K, K^17 ≤ n < K^(17·C₀), Δ ≤ 2^β₁ with 1 ≤ β₁ ≤ β, k ≤ β, β + 3 ≤
--   2^β ≤ n + 1, 0 < e ≤ 1, W = `WofU β K` ≤ A₁·K·e, and let the solver have the bound of the hypothesis
--   of Theorem D (a) at the index i. Then the exponent for one output with this Δ is at most
--   e·140·k·n·(β₁+1) + `ccD k C₀`·A₁·n·e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L162-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L162-L232

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

theorem RecursionToBound.needAt_le {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n Δ β₁ β A₁ : ℕ}
    (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n) (hlt : n < S.K i ^ (17 * C₀))
    (hβ₁ : 1 ≤ β₁) (hΔ : Δ ≤ 2 ^ β₁) (hββ : β₁ ≤ β) (hkβ : k ≤ β) (hbD : β + 3 ≤ 2 ^ β) (hD : 2 ^ β ≤ n + 1)
    (he0 : 0 < e) (he1 : e ≤ 1) (hM : ((WofU β (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needAt S k i n Δ : ℝ) ≤ e * (140 * (k : ℝ) * n * ((β₁ + 1 : ℕ) : ℝ)) + ((VariableBound.ccD k C₀ * A₁ : ℕ) : ℝ) * ((n : ℝ) * e) := by sorry
