-- Prove2me | Theorems.Thm_VariableBound_Search_round_inv
-- name    : VariableBound.Search.round_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:52.199117+00:00
-- url     : https://prove2.me/theorems/5aa1f47e-0ae6-4756-b83f-168975daf5f1
-- title:
--   Search: round inv
-- statement:
--   Under `Hyp`, one round keeps `Inv`; it leaves a list with X = 0 as it is and makes a list with X >
--   0 longer by one check. Here `evX` returns X(𝓛) on every list with these bounds (`StructD`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L227-L254
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L227-L254

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

theorem VariableBound.Search.round_inv (H : Hyp X m n nb rb tb fam) (evX : List (List ℕ) → ℤ) (hev : ∀ L, StructD m nb rb tb L → evX L = Xsum V nb (chksD m L))
    (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) :
    Inv V n nb rb tb fam (roundD evX fam m nb (beta n m nb) rb tb L) ∧
      (Xsum V nb (chksD m L) = 0 → roundD evX fam m nb (beta n m nb) rb tb L = L) ∧
      (Xsum V nb (chksD m L) ≠ 0 → (roundD evX fam m nb (beta n m nb) rb tb L).length = L.length + 1) := by sorry
