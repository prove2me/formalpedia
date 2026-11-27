-- Prove2me | Theorems.Thm_PeterfalviProblem_Witness_s_mem_P0
-- name    : PeterfalviProblem.Witness.s_mem_P0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:10:19.787539+00:00
-- url     : https://prove2.me/theorems/5a9bf9f4-bc51-4d78-81f5-a399bc0f6533
-- title:
--   Witness: s mem P0
-- statement:
--   The Witness construction uses the s mem P0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/Witness.lean#L132-L134
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Basic/Witness.lean#L132-L134

import Definitions.Def_PeterfalviProblem_Basic_FrobeniusGroup
import Definitions.Def_PeterfalviProblem_Basic_Witness
set_option autoImplicit false
open PeterfalviProblem
open scoped Pointwise
variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]
open PeterfalviProblem.Witness

theorem PeterfalviProblem.Witness.s_mem_P0 (data : Witness p q G) : data.s ∈ data.P0 := by sorry
