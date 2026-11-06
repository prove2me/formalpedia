-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_Fit_row_le
-- name    : VariableBound.Net.FitL.Fit.row_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:48:32.738857+00:00
-- url     : https://prove2.me/theorems/2431a734-b3ff-4fe6-8f02-d57f1af8435a
-- title:
--   Fit: row le
-- statement:
--   Every check of a list that is fit for an evaluation has at most 32Δ·⌈log(2Δ)⌉ clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L153-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L153-L158

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)

theorem VariableBound.Net.FitL.Fit.row_le {k n Δ nb M : ℕ} {D : Dat} (hF : Fit k n Δ nb M D) : ∀ L ∈ D.2, L.length ≤ sbMax Δ := by sorry
