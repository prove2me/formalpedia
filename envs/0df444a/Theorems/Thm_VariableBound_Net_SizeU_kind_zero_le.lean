-- Prove2me | Theorems.Thm_VariableBound_Net_SizeU_kind_zero_le
-- name    : VariableBound.Net.SizeU.kind_zero_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:14.056533+00:00
-- url     : https://prove2.me/theorems/6e4baf67-b9e4-415c-a90a-e6e3eb9c4888
-- title:
--   Size U: kind zero le
-- statement:
--   Step 3, «The total»: by display (59) with μ' = (k − 1)(n̄ + 1), kind 0 costs at most (k − 1)(n̄ + 1)·3·log(2Δ)
--   ≤ 3(k − 1)(n + log(2Δ)) bits. Needs 2 ≤ Δ, m ≤ Δn, the n̄ of the text, T₀ ≤ (k − 1)m and μ₀ ≤ (k − 1)(n̄ + 1),
--   and the inequalities of «Setting and parameters». For k = 1, where μ' = 0 and display (59) does not
--   apply, T₀ = μ₀ = 0 and the cost is 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L123-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeU.lean#L123-L158

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

theorem VariableBound.Net.SizeU.kind_zero_le (hp : ParamIneq) {k n Δ m nb T μ : ℕ} (hΔ : 2 ≤ Δ) (hm : m ≤ Δ * n) (hnb : IsNb n Δ nb) (hT : T ≤ (k - 1) * m)
    (hμ : μ ≤ (k - 1) * (nb + 1)) :
    lg (T.choose μ) ≤ ((k - 1 : ℕ) : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) ∧
      ((k - 1 : ℕ) : ℝ) * (nb + 1) * (3 * lg (2 * Δ)) ≤ 3 * (k - 1 : ℕ) * (n + lg (2 * Δ)) := by sorry
