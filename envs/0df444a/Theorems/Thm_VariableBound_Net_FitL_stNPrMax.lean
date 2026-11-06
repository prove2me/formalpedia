-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_stNPrMax
-- name    : VariableBound.Net.FitL.stNPrMax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:50:19.665292+00:00
-- url     : https://prove2.me/theorems/a26c3aae-6b84-4156-96c8-f310c19f3278
-- title:
--   Fit L: st NPr Max
-- statement:
--   Step 3, «Profiles»: for a list that is fit for an evaluation, the number of numbers that are
--   tried as profiles is at most `nPrMax`, which does not depend on the formula. Uses I ≤ r·s (`StNPr`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L162-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L162-L166

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

theorem VariableBound.Net.FitL.stNPrMax (h : StNPr) : StNPrMax := by sorry
