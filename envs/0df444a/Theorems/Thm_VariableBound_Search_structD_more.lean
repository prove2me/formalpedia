-- Prove2me | Theorems.Thm_VariableBound_Search_structD_more
-- name    : VariableBound.Search.structD_more
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:41:02.793209+00:00
-- url     : https://prove2.me/theorems/98eda668-5cff-47ce-9cbf-a264e6ace4b7
-- title:
--   Search: struct D more
-- statement:
--   The bounds of Step 2 on a list of checks, second case, under `Hyp`: a list with `Inv` and X > 0,
--   and one more candidate.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L213-L223
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L213-L223

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
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (fam : List (List ℕ))
variable {V n nb rb tb fam}

theorem VariableBound.Search.structD_more (H : Hyp X m n nb rb tb fam) (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) (hpos : 0 < Xsum V nb (chksD m L)) (l : List ℕ) (hl : l ∈ fam) :
    StructD m nb rb tb (L ++ [l]) := by sorry
