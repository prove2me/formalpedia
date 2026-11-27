-- Prove2me | Theorems.Thm_PeterfalviProblem_normOneUnits_card
-- name    : PeterfalviProblem.normOneUnits_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T05:02:22.517045+00:00
-- url     : https://prove2.me/theorems/d1c064e0-550e-445d-8b80-7d156679ffcc
-- title:
--   Peterfalvi Problem: norm One Units card
-- statement:
--   `|U| = (p^q - 1) / (p - 1)`. The norm map `Fˣ → 𝔽_pˣ` is onto, and `U` is its kernel.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L63-L80
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L63-L80

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

theorem PeterfalviProblem.normOneUnits_card [Fact p.Prime] (hq : q ≠ 0) :
    Nat.card (normOneUnits p q) = (p ^ q - 1) / (p - 1) := by sorry
