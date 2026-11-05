-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_kind_one_le
-- name    : VariableBound.Net.SizeU.kind_one_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:43.579624+00:00
-- url     : https://prove2.me/theorems/ae590a57-adec-4535-8267-38f4a6cc2813
-- title:
--   Size U: kind one le
-- statement:
--   Step 3, «The total»: «With μ' = kM and 3T₁/μ' ≤ 3s̄ (as r ≤ M), kind 1 costs at most kM·log(3s̄)
--   bits», where s̄ = 16m/n̄; this is at most kM·log(96Δ·log(2Δ)), as 3s̄ < 96Δ·log(2Δ). Needs 2 ≤ Δ, n̄
--   < m ≤ Δn, the n̄ of the text, k ≥ 1, r ≤ M, M ≥ 1,
--   I ≤ r·s̄ (as n̄·I ≤ r·16m), T₁ ≤ kI and μ₁ ≤ kM, and the inequalities of «Setting and parameters».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L164-L200
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L164-L200

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}

theorem VariableBound.Net.SizeU.kind_one_le (hp : ParamIneq) {k n Δ m nb M r I T μ : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (hnb : IsNb n Δ nb) (hk : 1 ≤ k) (hr : r ≤ M)
    (hM : 1 ≤ M) (hI : nb * I ≤ r * (16 * m)) (hT : T ≤ k * I) (hμ : μ ≤ k * M) :
    lg (T.choose μ) ≤ k * M * lg (3 * (16 * m / nb)) ∧ (k : ℝ) * M * lg (3 * (16 * m / nb)) ≤ k * M * lg (96 * Δ * lg (2 * Δ)) := by sorry
