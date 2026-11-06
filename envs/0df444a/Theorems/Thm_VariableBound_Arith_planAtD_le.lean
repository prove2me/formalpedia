-- Prove2me | Theorems.Thm_VariableBound_Arith_planAtD_le
-- name    : VariableBound.Arith.planAtD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:48.651508+00:00
-- url     : https://prove2.me/theorems/b286d4a8-c4ac-4eb5-a542-7cf40da185d4
-- title:
--   Arith: plan At D le
-- statement:
--   The statement at one level: for k ≥ 1, a polynomial-time solver with K ≥ 2 nodes at the index i
--   and the bound need(λ, B) ≤ e·K²·λ + C₀·K²·log₂(K·(λ+B)), K^17 ≤ n < K^(17·C₀), 2^(−s) ≤ e ≤ 1,
--   1/(log₂ K)^C₀ ≤ e,
--   2^s ≤ (2/e)^C and B·k² ≤ ⌊log₂ n⌋, the exponent of the plan, or else n, is at most A·k²·n·e·(s+1),
--   with A = `AexpD C₀` and B = `BkD C C₀`; from the interface statements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L70-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L70-L121

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_UniformInK_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithTop
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith

theorem VariableBound.Arith.planAtD_le (hN : StNeedD) (hP : StPlanLeD) (hPN : StPlanNeedD) (hM : StMasterU) (hDL : StDLogU) (h6 : StSixU) (hB : StBetaU)
    {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (i : Idx) {e : ℝ} {C C₀ k n s : ℕ} (hk : 1 ≤ k) (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (he1 : e ≤ 1) (hs : 1 / (2 : ℝ) ^ s ≤ e) (heK : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B)))
    (hBk : BkD C C₀ * k ^ 2 ≤ Nat.log 2 n) :
    (((planAtD S k n i s).getD n : ℕ) : ℝ) ≤ (AexpD C₀ : ℝ) * (k : ℝ) ^ 2 * n * e * ((s : ℝ) + 1) := by sorry
