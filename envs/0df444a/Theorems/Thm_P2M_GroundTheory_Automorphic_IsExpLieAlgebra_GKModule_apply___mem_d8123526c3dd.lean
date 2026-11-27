-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_d8123526c3dd
-- name    : P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_d8123526c3dd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:37.721099+00:00
-- url     : https://prove2.me/theorems/219f033b-0efd-5f13-a103-55df40558bfc
-- title:
--   P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem d8123526c3dd: P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem d8123526c3dd
-- statement:
--   The P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem d8123526c3dd construction uses the P2 M Ground Theory Automorphic Is Exp Lie Algebra GKModule apply   mem d8123526c3dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L49-L51

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

theorem P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_d8123526c3dd (M : h.GKModule K V) (Y : Subrepresentation M.rep)
    (X : h.lieSubalgebra) {y : V} (hy : y ∈ Y.toSubmodule) : M.ρ X y ∈ Y.toSubmodule := by sorry

alias «GroundTheory».«Automorphic».«IsExpLieAlgebra».«GKModule».«apply_ρ_mem» := P2M_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_apply___mem_d8123526c3dd
