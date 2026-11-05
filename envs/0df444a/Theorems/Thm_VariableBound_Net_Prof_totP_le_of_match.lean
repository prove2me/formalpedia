-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_totP_le_of_match
-- name    : VariableBound.Net.Prof.totP_le_of_match
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:44:12.631803+00:00
-- url     : https://prove2.me/theorems/abc7f4f9-200e-4ed3-a688-9d2f39c5ebb5
-- title:
--   Prof: tot P le of match
-- statement:
--   Step 3, «Profiles»: the profile y of a term has Σ_({a,b}) μ_(a,b,κ) ≤ (k − 1 + κ)·Σ_a μ_(a,κ).
--   Needs 0 < g, well-formed data, that P is a set of positions of objects, κ < 2, and that P belongs to
--   y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L270-L274
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L270-L274

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
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.totP_le_of_match {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) {y : ℕ}
    (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) : totP g D y κ ≤ (k - 1 + κ) * tot g D y κ := by sorry
