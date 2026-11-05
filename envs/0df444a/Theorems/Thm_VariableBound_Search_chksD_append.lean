-- Prove2me | Theorems.Thm_VariableBound_Search_chksD_append
-- name    : VariableBound.Search.chksD_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:08:17.290494+00:00
-- url     : https://prove2.me/theorems/5a54259f-978a-493e-b886-0f9f26f6c00b
-- title:
--   Search: chks D append
-- statement:
--   The list (𝓛, l) of lists of numbers is the list (𝓛, Γ) of sets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L45-L46

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
set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset

theorem VariableBound.Search.chksD_append (m : ℕ) (L : List (List ℕ)) (l : List ℕ) : chksD m (L ++ [l]) = chksD m L ++ [Fld.setD m l] := by sorry
