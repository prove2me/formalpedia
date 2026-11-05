-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_totP_eq
-- name    : VariableBound.Net.Prof.totP_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:25.795385+00:00
-- url     : https://prove2.me/theorems/cf040fa8-16d7-4075-bf95-c6f97b5c9668
-- title:
--   Prof: tot P eq
-- statement:
--   `totP` is Σ_({a,b}) μ_(a,b,κ), as a sum over the pairs a < b < g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L69-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L69-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.totP_eq (g : ℕ) (D : Dat) (y κ : ℕ) : totP g D y κ = ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b κ := by sorry
