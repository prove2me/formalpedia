-- Prove2me | Theorems.Thm_PeterfalviProblem_conj_layer_of_exp
-- name    : PeterfalviProblem.conj_layer_of_exp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-27T05:01:51.781324+00:00
-- url     : https://prove2.me/theorems/4119f32d-1df0-44a8-a19f-6f6a234eac97
-- title:
--   Peterfalvi Problem: conj layer of exp
-- statement:
--   Suppose that `g v = vᵉ g`. Then `(z^g)^v = (z^{vᵉ})^g`, where `z^g = g⁻¹ z g`.
--
--   Source: https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Proof/GroupIdentities.lean#L161-L165
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Proof/GroupIdentities.lean#L161-L165

import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Definitions.Def_PeterfalviProblem_Proof_GroupIdentities
set_option autoImplicit false
open PeterfalviProblem
variable {G : Type*} [Group G]
variable {a₀ a₁ a₂ b₀ b₁ b₂ : G}

theorem PeterfalviProblem.conj_layer_of_exp {g v : G} {e : ℕ} (hexp : g * v = v ^ e * g) (z : G) :
    v⁻¹ * (g⁻¹ * z * g) * v = g⁻¹ * ((v ^ e)⁻¹ * z * v ^ e) * g := by sorry
