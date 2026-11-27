-- Prove2me | Theorems.Thm_PeterfalviProblem_normN_eq_algebraMap_norm
-- name    : PeterfalviProblem.normN_eq_algebraMap_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:09:31.714354+00:00
-- url     : https://prove2.me/theorems/76f938ee-8d79-4915-b647-dc3a99d9ae79
-- title:
--   Peterfalvi Problem: norm N eq algebra Map norm
-- statement:
--   The product `normN` is Mathlib's norm `Algebra.norm (ZMod p)`, viewed in `𝔽_{p^q}`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L42-L45
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/NormOneUnits.lean#L42-L45

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

theorem PeterfalviProblem.normN_eq_algebraMap_norm [Fact p.Prime] (hq : q ≠ 0) (x : GaloisField p q) :
    normN p q x = algebraMap (ZMod p) (GaloisField p q) (Algebra.norm (ZMod p) x) := by sorry
