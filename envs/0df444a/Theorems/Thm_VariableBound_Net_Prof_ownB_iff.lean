-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_ownB_iff
-- name    : VariableBound.Net.Prof.ownB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:56.794189+00:00
-- url     : https://prove2.me/theorems/03f26aa7-281d-4a08-b8a0-246c7eead2d5
-- title:
--   Prof: own B iff
-- statement:
--   What `ownB` says: a is touched, and no smaller node is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L97-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L97-L102

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_ownB_iff

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.ownB_iff {g n : ℕ} {D : Dat} {o a : ℕ} :
    ownB g n D o a = true ↔ tchB g n D a o = true ∧ ∀ c < g, c < a → tchB g n D c o = false := by sorry
