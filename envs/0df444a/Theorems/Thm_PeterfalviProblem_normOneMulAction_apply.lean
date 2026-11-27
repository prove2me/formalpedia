-- Prove2me | Theorems.Thm_PeterfalviProblem_normOneMulAction_apply
-- name    : PeterfalviProblem.normOneMulAction_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T05:05:17.656293+00:00
-- url     : https://prove2.me/theorems/04a8549a-ae88-5845-997c-47018d27d7d9
-- title:
--   Peterfalvi Problem: norm One Mul Action apply
-- statement:
--   The Peterfalvi Problem construction uses the norm One Mul Action apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/FrobeniusGroup.lean#L35-L38
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/FrobeniusGroup.lean#L35-L38

import Definitions.Def_PeterfalviProblem_Basic_NormOneUnits
import Definitions.Def_PeterfalviProblem_Basic_FrobeniusGroup
set_option autoImplicit false
open PeterfalviProblem
variable (p q : ℕ) [Fact p.Prime]

theorem PeterfalviProblem.normOneMulAction_apply (u : normOneUnits p q) (s : GaloisField p q) :
    ((normOneMulAction p q u) (Multiplicative.ofAdd s)).toAdd =
      ((u : (GaloisField p q)ˣ) : GaloisField p q) * s := by sorry

attribute [defeq] PeterfalviProblem.normOneMulAction_apply
