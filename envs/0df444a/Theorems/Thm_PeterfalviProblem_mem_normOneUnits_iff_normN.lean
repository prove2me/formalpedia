-- Prove2me | Theorems.Thm_PeterfalviProblem_mem_normOneUnits_iff_normN
-- name    : PeterfalviProblem.mem_normOneUnits_iff_normN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:10:07.614022+00:00
-- url     : https://prove2.me/theorems/b6f1401f-d75d-458b-862d-4d8194a36d51
-- title:
--   Peterfalvi Problem: mem norm One Units iff norm N
-- statement:
--   The Peterfalvi Problem construction uses the mem norm One Units iff norm N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L47-L58
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L47-L58

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

theorem PeterfalviProblem.mem_normOneUnits_iff_normN [Fact p.Prime] (hq : q ≠ 0) (u : (GaloisField p q)ˣ) :
    u ∈ normOneUnits p q ↔ normN p q (u : GaloisField p q) = 1 := by sorry
