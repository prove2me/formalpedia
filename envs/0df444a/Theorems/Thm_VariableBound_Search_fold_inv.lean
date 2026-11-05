-- Prove2me | Theorems.Thm_VariableBound_Search_fold_inv
-- name    : VariableBound.Search.fold_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:36.944206+00:00
-- url     : https://prove2.me/theorems/5bb0c124-05eb-4be4-b2e3-f6b95ebd2c80
-- title:
--   Search: fold inv
-- statement:
--   Under `Hyp`, after j rounds the list has `Inv`, and X = 0 or it has j checks. Here `evX` returns
--   X(𝓛) on every list with these bounds (`StructD`), and the word of every such list fits under the
--   pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L259-L281
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L259-L281

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

theorem VariableBound.Search.fold_inv (H : Hyp X m n nb rb tb fam) (pad : U) (evX : List (List ℕ) → ℤ) (hev : ∀ L, StructD m nb rb tb L → evX L = Xsum V nb (chksD m L))
    (hpad : ∀ L, StructD m nb rb tb L → len L ≤ pad.length) (j : ℕ) :
    Inv V n nb rb tb fam ((List.range j).foldl (fun L _ => cap pad [] (roundD evX fam m nb (beta n m nb) rb tb L)) (cap pad [] [])) ∧
      (Xsum V nb (chksD m ((List.range j).foldl (fun L _ => cap pad [] (roundD evX fam m nb (beta n m nb) rb tb L)) (cap pad [] []))) = 0 ∨
        ((List.range j).foldl (fun L _ => cap pad [] (roundD evX fam m nb (beta n m nb) rb tb L)) (cap pad [] [])).length = j) := by sorry
