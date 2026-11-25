-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_6086aaa81b9a
-- name    : P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_6086aaa81b9a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:42.527579+00:00
-- url     : https://prove2.me/theorems/46c50716-29e7-5f87-aef2-23091059876f
-- title:
--   P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem 6086aaa81b9a: P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem 6086aaa81b9a
-- statement:
--   The P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem 6086aaa81b9a construction uses the P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem 6086aaa81b9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L45-L47

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
attribute [local instance 100] LieRing.ofAssociativeRing
open Set Module
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_6086aaa81b9a (M : h.GKModule K V) (Y : Subrepresentation M.rep) (k : K) {y : V}
    (hy : y ∈ Y.toSubmodule) : M.σ k y ∈ Y.toSubmodule := by sorry

alias «GroundTheory».«Automorphic».«IsExpLieAlgebra».«GKModule».«apply_σ_mem» := P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_6086aaa81b9a
