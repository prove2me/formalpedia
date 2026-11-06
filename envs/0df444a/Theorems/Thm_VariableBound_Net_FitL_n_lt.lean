-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_n_lt
-- name    : VariableBound.Net.FitL.n_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:48:38.493803+00:00
-- url     : https://prove2.me/theorems/1e14d3bc-e929-4aab-8d06-23e9982b96c4
-- title:
--   Fit L: n lt
-- statement:
--   n/(2·log(2Δ)) < n̄ gives n < 2n̄·⌈log(2Δ)⌉.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L93-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L93-L96

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

theorem VariableBound.Net.FitL.n_lt {n Δ nb : ℕ} (h : AppVariables.IsNb n Δ nb) : n < LD Δ * (2 * nb) := by sorry
