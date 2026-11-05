-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_adm_iff
-- name    : VariableBound.Net.Prof.adm_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:23.417716+00:00
-- url     : https://prove2.me/theorems/e3d49250-5edc-4f00-8046-50f82c904c3d
-- title:
--   Prof: adm iff
-- statement:
--   What `admD` says.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L279-L294
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L279-L294

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_iff
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.adm_iff (k g n nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ) : admD k g n nb M D fl y = true ↔
    (if fl = true then tot g D y 0 ≤ nb else tot g D y 0 = nb + 1) ∧ tot g D y 1 ≤ M ∧ ∀ κ < 2,
      totP g D y κ ≤ (k - 1 + κ) * tot g D y κ ∧
      ∀ a < g, ∀ b < g, (b < a → digit (objs D).length y ((a * g + b) * 2 + κ) = 0) ∧
        (a < b → mu g D y a b κ ≤ (tst g n D a b κ).length) := by sorry
