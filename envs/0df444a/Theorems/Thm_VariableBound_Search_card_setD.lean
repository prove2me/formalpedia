-- Prove2me | Theorems.Thm_VariableBound_Search_card_setD
-- name    : VariableBound.Search.card_setD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:44.627351+00:00
-- url     : https://prove2.me/theorems/33205042-90fd-4fb3-8df5-bb9a8991a0c9
-- title:
--   Search: card set D
-- statement:
--   A list of distinct numbers below m has as many members as its set of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L75-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L75-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset

theorem VariableBound.Search.card_setD (m : ℕ) (l : List ℕ) (h1 : l.Nodup) (h2 : ∀ E ∈ l, E < m) : #(Fld.setD m l) = l.length := by sorry
