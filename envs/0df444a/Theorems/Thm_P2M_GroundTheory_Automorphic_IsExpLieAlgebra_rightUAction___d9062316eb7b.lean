-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
-- name    : P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:01.535338+00:00
-- url     : https://prove2.me/theorems/4ffd70bf-4124-4742-b04a-1bb65884fa0c
-- title:
--   P2 M Ground Theory Automorphic Is Exp Lie Algebra right UAction   d9062316eb7b: P2 M Ground Theory Automorphic Is Exp Lie Algebra right UAction   d9062316eb7b
-- statement:
--   The P2 M Ground Theory Automorphic Is Exp Lie Algebra right UAction   d9062316eb7b construction uses the P2 M Ground Theory Automorphic Is Exp Lie Algebra right UAction   d9062316eb7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/RightRegular.lean#L232-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/RightRegular.lean#L232-L234

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
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
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
attribute [local instance 100] LieRing.ofAssociativeRing

theorem P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b (X : h.lieSubalgebra) :
    h.rightUAction (F := F) (UniversalEnvelopingAlgebra.ι ℝ X) = h.rightDerivEnd (h.ofLie X) := by sorry

alias «GroundTheory».«Automorphic».«IsExpLieAlgebra».«rightUAction_ι» := P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
