-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_mem_sympGroup_964162e978e0
-- name    : P2M_GroundTheory_Heights__Theta_mem_sympGroup_964162e978e0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:25.229114+00:00
-- url     : https://prove2.me/theorems/9b89fb72-22fb-53a1-b571-6618c1a1a18e
-- title:
--   P2 M Ground Theory Heights  Theta mem symp Group 964162e978e0: P2 M Ground Theory Heights  Theta mem symp Group 964162e978e0
-- statement:
--   The P2 M Ground Theory Heights  Theta mem symp Group 964162e978e0 construction uses the P2 M Ground Theory Heights  Theta mem symp Group 964162e978e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/WeilPolarization/WmSysObjects.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/WeilPolarization/WmSysObjects.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_WeilPolarization_WmSysObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Matrix
set_option linter.unusedSectionVars false
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem P2M_GroundTheory_Heights__Theta_mem_sympGroup_964162e978e0 {ω : LinearMap.BilinForm R W} {g : W ≃ₗ[R] W} :
    g ∈ sympGroup ω ↔ ∀ w w', ω (g w) (g w') = ω w w' := by sorry

alias «GroundTheory».«Heights₂».«Theta».«mem_sympGroup» := P2M_GroundTheory_Heights__Theta_mem_sympGroup_964162e978e0
