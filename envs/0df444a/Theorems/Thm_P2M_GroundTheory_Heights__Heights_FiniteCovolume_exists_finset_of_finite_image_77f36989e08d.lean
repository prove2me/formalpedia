-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_finset_of_finite_image_77f36989e08d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_finset_of_finite_image_77f36989e08d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:22.232296+00:00
-- url     : https://prove2.me/theorems/e50ecd71-4d0e-41b5-b3af-5a3332c7ee89
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume exists finset of finite image 77f36989e08d: P2 M Ground Theory Heights  Heights Finite Covolume exists finset of finite image 77f36989e08d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume exists finset of finite image 77f36989e08d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume exists finset of finite image 77f36989e08d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L12-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_finset_of_finite_image_77f36989e08d {α β : Type*} (s : Set α) (f : α → β) (hf : (f '' s).Finite)
    (P : α → α → Prop) (hP : ∀ x ∈ s, ∀ y ∈ s, f x = f y → P y x) :
    ∃ S : Finset α, (S : Set α) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ S, P y x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«exists_finset_of_finite_image» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_finset_of_finite_image_77f36989e08d
