-- Prove2me | Theorems.Thm_PeterfalviProblem_Paley_card_paleySet_lower
-- name    : PeterfalviProblem.Paley.card_paleySet_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:05:33.2934+00:00
-- url     : https://prove2.me/theorems/7c74eead-b5a1-4a08-a592-0c6bd4af6074
-- title:
--   Paley: card paley Set lower
-- statement:
--   The Paley set is large: `|F| - 3 ≤ 4 |T|`. (In fact `|T| = (|F| - 3)/4`, but we need only
--   this bound.)
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L145-L202
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean#L145-L202

import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
set_option autoImplicit false
open PeterfalviProblem PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]

theorem PeterfalviProblem.Paley.card_paleySet_lower [Fintype F] (h30 : (3 : F) = 0) (hnegsq : ¬ IsSquare (-1 : F))
    (T : Finset F) (hT : ∀ a, a ∈ T ↔ a ∈ paleySet F) : Fintype.card F - 3 ≤ 4 * #T := by sorry
