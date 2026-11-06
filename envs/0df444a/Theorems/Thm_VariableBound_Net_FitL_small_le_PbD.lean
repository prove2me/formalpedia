-- Prove2me | Theorems.Thm_VariableBound_Net_FitL_small_le_PbD
-- name    : VariableBound.Net.FitL.small_le_PbD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:48:31.068633+00:00
-- url     : https://prove2.me/theorems/3a51e1ad-0d35-44f9-bf30-0db937aebafe
-- title:
--   Fit L: small le Pb D
-- statement:
--   On g = 3K⁸ nodes, P = 2⌈n/g⌉(1 + Δ), the size for m ≤ n̄, is at most `PbD`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L222-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean#L222-L231

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

theorem VariableBound.Net.FitL.small_le_PbD (K n Δ : ℕ) : 2 * (qv (3 * K ^ 8) n * (1 + Δ)) ≤ PbD K n Δ := by sorry
