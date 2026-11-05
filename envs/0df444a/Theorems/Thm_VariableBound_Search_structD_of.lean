-- Prove2me | Theorems.Thm_VariableBound_Search_structD_of
-- name    : VariableBound.Search.structD_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:08:34.86723+00:00
-- url     : https://prove2.me/theorems/ebc00cdc-996f-404c-9658-64e736fe7989
-- title:
--   Search: struct D of
-- statement:
--   Under `Hyp`, the bounds of Step 2 on the number of checks, their sizes and the loads pass from
--   sets to lists of numbers, for a list of candidates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L193-L202
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L193-L202

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
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (fam : List (List ℕ))
variable {V n nb rb tb fam}

theorem VariableBound.Search.structD_of (H : Hyp X m n nb rb tb fam) (L : List (List ℕ)) (hm : ∀ l ∈ L, l ∈ fam)
    (h : (chksD m L).length ≤ rb ∧ (∀ Λ ∈ chksD m L, nb * #Λ ≤ 16 * Fintype.card (Fin m)) ∧ ∀ e : Fin m, load (chksD m L) e ≤ tb + 2) :
    StructD m nb rb tb L := by sorry
