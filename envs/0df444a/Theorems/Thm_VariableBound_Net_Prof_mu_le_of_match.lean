-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_mu_le_of_match
-- name    : VariableBound.Net.Prof.mu_le_of_match
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:03.082669+00:00
-- url     : https://prove2.me/theorems/b180b0ad-ef2c-4688-b842-fa9c845ff813
-- title:
--   Prof: mu le of match
-- statement:
--   Step 3, «Profiles»: the profile y of a term has μ_(a,b,κ) ≤ t_(a,b,κ), for nodes a ≠ b below g
--   and κ < 2, if P belongs to y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L262-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L262-L265

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

theorem VariableBound.Net.Prof.mu_le_of_match {g n : ℕ} {D : Dat} {P : Finset ℕ} {y : ℕ} (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hne : b ≠ a) : mu g D y a b κ ≤ (tst g n D a b κ).length := by sorry
