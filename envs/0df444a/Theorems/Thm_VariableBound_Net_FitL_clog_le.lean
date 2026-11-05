-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_clog_le
-- name    : VariableBound.Net.FitL.clog_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:50:08.635354+00:00
-- url     : https://prove2.me/theorems/01e477b6-303d-4c64-9df9-649a03762359
-- title:
--   Fit L: clog le
-- statement:
--   ⌈log(96Δ·⌈log(2Δ)⌉)⌉ ≤ 2·⌈log(2Δ)⌉ + 5 for Δ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L70-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L70-L79

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

theorem VariableBound.Net.FitL.clog_le {Δ : ℕ} (hΔ : 2 ≤ Δ) : Nat.clog 2 (96 * Δ * LD Δ) ≤ 2 * LD Δ + 5 := by sorry
