-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_row_le
-- name    : VariableBound.Net.FitL.row_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:03:38.346825+00:00
-- url     : https://prove2.me/theorems/7fd486b2-f0ac-4934-b455-b92a3b5ec4c5
-- title:
--   Fit L: row le
-- statement:
--   A check of at most s̄ = 16m/n̄ clauses, with m ≤ Δn and n̄ as in «Setting and parameters» of
--   Appendix D, has at most 32Δ·⌈log(2Δ)⌉ clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L100-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L100-L105

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

theorem VariableBound.Net.FitL.row_le {n Δ nb m l : ℕ} (h : AppVariables.IsNb n Δ nb) (hm : m ≤ Δ * n) (hl : nb * l ≤ 16 * m) : l ≤ sbMax Δ := by sorry
