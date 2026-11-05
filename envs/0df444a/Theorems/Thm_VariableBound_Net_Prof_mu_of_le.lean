-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_mu_of_le
-- name    : VariableBound.Net.Prof.mu_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:54.978429+00:00
-- url     : https://prove2.me/theorems/e7ef3e52-34b8-490a-a39e-3f6bcd886fa8
-- title:
--   Prof: mu of le
-- statement:
--   For a ≤ b the number that the profile prescribes is the digit at the place (a·g + b)·2 + κ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L56-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L56-L58

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_of_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.mu_of_le (g : ℕ) (D : Dat) (y : ℕ) {a b : ℕ} (h : a ≤ b) (κ : ℕ) :
    mu g D y a b κ = digit (objs D).length y ((a * g + b) * 2 + κ) := by sorry
