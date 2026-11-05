-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_two_le_LD
-- name    : VariableBound.Net.FitL.two_le_LD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:03:22.429541+00:00
-- url     : https://prove2.me/theorems/8d380a2a-61c1-4113-9cef-fdb24fb73cfb
-- title:
--   Fit L: two le LD
-- statement:
--   ⌈log(2Δ)⌉ ≥ 2 for Δ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L48-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L48-L50

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
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)

theorem VariableBound.Net.FitL.two_le_LD {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ≤ LD Δ := by sorry
