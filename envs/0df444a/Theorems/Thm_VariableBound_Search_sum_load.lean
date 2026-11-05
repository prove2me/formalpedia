-- Prove2me | Theorems.Thm_VariableBound_Search_sum_load
-- name    : VariableBound.Search.sum_load
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:40.488327+00:00
-- url     : https://prove2.me/theorems/203b80bf-ea48-4039-b67d-6fcf3cb1cda0
-- title:
--   Search: sum load
-- statement:
--   Σ_E 2^load(E) is `loadSum`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L68-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L68-L72

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

theorem VariableBound.Search.sum_load (m : ℕ) (L : List (List ℕ)) : ∑ e : Fin m, (2 : ℚ) ^ load (chksD m L) e = (loadSum m L : ℚ) := by sorry
