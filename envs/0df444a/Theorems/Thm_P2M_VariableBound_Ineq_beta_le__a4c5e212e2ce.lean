-- Prove2me | Theorems.Thm_P2M_VariableBound_Ineq_beta_le__a4c5e212e2ce
-- name    : P2M_VariableBound_Ineq_beta_le__a4c5e212e2ce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:25.700964+00:00
-- url     : https://prove2.me/theorems/7f6ed447-772a-4a2e-b37d-1df246739b0d
-- title:
--   P2 M Variable Bound Ineq beta le  a4c5e212e2ce: P2 M Variable Bound Ineq beta le  a4c5e212e2ce
-- statement:
--   β ≤ n + 3(n̄+1)·log(2Δ) + 2, for 2 ≤ Δ and n̄ < m ≤ Δ·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L101-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L101-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq

theorem P2M_VariableBound_Ineq_beta_le__a4c5e212e2ce {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) :
    (beta n m nb : ℝ) ≤ n + 3 * (nb + 1) * lg (2 * Δ) + 2 := by sorry

alias «VariableBound».«Ineq».«beta_le₁» := P2M_VariableBound_Ineq_beta_le__a4c5e212e2ce
