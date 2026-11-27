-- Prove2me | Theorems.Thm_PeterfalviProblem_pow_three_eq_conj_mul
-- name    : PeterfalviProblem.pow_three_eq_conj_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-27T04:59:23.800848+00:00
-- url     : https://prove2.me/theorems/0fe953b0-eb94-4a40-aa1a-2fbe549d3df2
-- title:
--   Peterfalvi Problem: pow three eq conj mul
-- statement:
--   If `x³ = 1`, then `(x c)³ = c^{x²} · c^x · c`, where `c^x = x⁻¹ c x`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Proof/GroupIdentities.lean#L55-L59
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Proof/GroupIdentities.lean#L55-L59

import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Definitions.Def_PeterfalviProblem_Proof_GroupIdentities
set_option autoImplicit false
open PeterfalviProblem
variable {G : Type*} [Group G]
variable {x c g : G}

theorem PeterfalviProblem.pow_three_eq_conj_mul (hx : x ^ 3 = 1) (c : G) :
    (x * c) ^ 3 = x⁻¹ * (x⁻¹ * c * x) * x * ((x⁻¹ * c * x) * c) := by sorry
