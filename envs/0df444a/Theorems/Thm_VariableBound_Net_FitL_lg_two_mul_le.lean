-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_lg_two_mul_le
-- name    : VariableBound.Net.FitL.lg_two_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:54:35.370574+00:00
-- url     : https://prove2.me/theorems/a0f8ef21-2951-4af6-b04a-f52864b87ce9
-- title:
--   Fit L: lg two mul le
-- statement:
--   log(2Δ) ≤ ⌈log(2Δ)⌉.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L64-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L64-L67

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

theorem VariableBound.Net.FitL.lg_two_mul_le (Δ : ℕ) : lg (2 * Δ) ≤ LD Δ := by sorry
