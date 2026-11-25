-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
-- name    : P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:33.135446+00:00
-- url     : https://prove2.me/theorems/441d0223-6eff-4266-80e3-3da21242a791
-- title:
--   P2 M Ground Theory Automorphic Is Exp Lie Algebra gk Module   apply af7e43e2c7fe: P2 M Ground Theory Automorphic Is Exp Lie Algebra gk Module   apply af7e43e2c7fe
-- statement:
--   The P2 M Ground Theory Automorphic Is Exp Lie Algebra gk Module   apply af7e43e2c7fe construction uses the P2 M Ground Theory Automorphic Is Exp Lie Algebra gk Module   apply af7e43e2c7fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L314-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L314-L315

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (K : Subgroup G)

theorem P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe [CompleteSpace E] (X : h.lieSubalgebra) (v : h.gkVectors π K) :
    (((h.gkModule π K).ρ X v : h.gkVectors π K) : E) = h.derivOp π (h.ofLie X) v := by sorry

alias «GroundTheory».«Automorphic».«IsExpLieAlgebra».«gkModule_ρ_apply» := P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe

attribute [defeq] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
