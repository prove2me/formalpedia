-- Prove2me | Theorems.Thm_PeterfalviProblem_card_galoisField_three_mod_four
-- name    : PeterfalviProblem.card_galoisField_three_mod_four
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:02:07.978103+00:00
-- url     : https://prove2.me/theorems/327cd566-933d-4518-95a6-74f50949241a
-- title:
--   Peterfalvi Problem: card galois Field three mod four
-- statement:
--   `|𝔽_{3^q}| ≡ 3 (mod 4)` when `q` is odd.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L152-L158
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L152-L158

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_PeterfalviProblem_Algebra_PaleySet
import Definitions.Def_PeterfalviProblem_Statement
import Definitions.Def_PeterfalviProblem_Basic_NormOneUnits
set_option autoImplicit false
open PeterfalviProblem
variable (p q : ℕ)
variable {p q}

theorem PeterfalviProblem.card_galoisField_three_mod_four (hq0 : q ≠ 0) (hqodd : Odd q)
    [Fintype (GaloisField 3 q)] : Fintype.card (GaloisField 3 q) % 4 = 3 := by sorry
