-- Prove2me | Theorems.Thm_SplitCount_engineBy_runs
-- name    : SplitCount.engineBy_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:56.505031+00:00
-- url     : https://prove2.me/theorems/f5329acd-c46c-4c23-adaf-88957c551685
-- title:
--   Split Count: engine By runs
-- statement:
--   The procedure counts: under the hypotheses of `StSuffices` there is a constant c such that, on
--   (n in unary, ψ) for ψ with clauses of at most k literals on x₀ … xₙ₋₁, `engineBy step D` returns the
--   number of satisfying assignments of ψ on n variables in n + 1 bits within c·2^{δn} steps, on states
--   of size at most c·M^c, for every M ≥ 1 with n ≤ M and at most M clauses in ψ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Suffices.lean#L45-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Suffices.lean#L45-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Leaf
import Definitions.Def_CountKSat_Walk
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Suffices
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify Paper CountKSat Eight Eight.Width Occ

theorem SplitCount.engineBy_runs {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {step : CNode → Option (CNode × CNode)} {Dd Bl Sk : ℕ} (hsp : SparsifiesPlain k (δ / 3) step Dd Bl Sk)
    {D : StepMachine (List Unit × Fml) ℕ} {δ' : ℝ} {A : ℕ} (hδ' : 0 ≤ δ') (hδB : δ' * ((1 + 3 * (((max k 3 : ℕ) : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3) (hD : CountsThree D δ' A) :
    ∃ c : ℕ, ∀ (n : ℕ) (ψ : Fml) (M : ℕ), (∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) → n ≤ M → ψ.length ≤ M → 1 ≤ M →
      ∃ T : ℕ, (engineBy step D).Runs (List.replicate n (), ψ) T (c * M ^ c) (SatK.binary n (cntN n ψ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by sorry
