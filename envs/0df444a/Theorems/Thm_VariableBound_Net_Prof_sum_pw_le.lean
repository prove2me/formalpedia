-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_sum_pw_le
-- name    : VariableBound.Net.Prof.sum_pw_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:34.725122+00:00
-- url     : https://prove2.me/theorems/9e192196-1a1d-4013-819b-49d1a2571002
-- title:
--   Prof: sum pw le
-- statement:
--   Step 3, «Profiles»: Σ_({a,b}) μ_(a,b,κ) ≤ (k − 1 + κ)·Σ_a μ_(a,κ). Here for the numbers of P:
--   the members of kind κ with the test {a, b}, summed over the pairs a < b < g, are at most k − 1 + κ
--   times the
--   members of kind κ. Needs 0 < g, well-formed data, and that P is a set of positions of objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L213-L239
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L213-L239

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_pw_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.sum_pw_le {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (κ : ℕ) :
    ∑ b ∈ range g, ∑ a ∈ range b, pw g n D P a b κ ≤ (k - 1 + κ) * (kP D P κ).card := by sorry
