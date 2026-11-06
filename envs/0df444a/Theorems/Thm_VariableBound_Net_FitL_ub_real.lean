-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_ub_real
-- name    : VariableBound.Net.FitL.ub_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:48:36.555713+00:00
-- url     : https://prove2.me/theorems/5588a05f-c6ea-40c8-81a0-a31c3227d089
-- title:
--   Fit L: ub real
-- statement:
--   The right side of the bound on U displayed in Step 3 of Appendix D, on g = 3K⁸ nodes, is at most
--   `UbD`, for Δ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L208-L219
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L208-L219

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Net_Fit
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)

theorem VariableBound.Net.FitL.ub_real (k K n : ℕ) {Δ : ℕ} (hΔ : 2 ≤ Δ) :
    6 * (k : ℝ) * (n + lg (2 * Δ)) + 28 * k * n * lg (96 * Δ * lg (2 * Δ)) + 2 * ((3 * K ^ 8 : ℕ) : ℝ) ^ 2 ≤ ((UbD k K n Δ : ℕ) : ℝ) := by sorry
