-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FlatBC_subEquiv_one_tmul_19804f52a53f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FlatBC_subEquiv_one_tmul_19804f52a53f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:26.167927+00:00
-- url     : https://prove2.me/theorems/61590a66-7a02-4d53-a666-d354793986f1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Flat BC sub Equiv one tmul 19804f52a53f: P2 M Ground Theory Heights  Heights Kleiman Flat BC sub Equiv one tmul 19804f52a53f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Flat BC sub Equiv one tmul 19804f52a53f construction uses the P2 M Ground Theory Heights  Heights Kleiman Flat BC sub Equiv one tmul 19804f52a53f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechFlat.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechFlat.lean#L101-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open TensorProduct MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.FlatBC
variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']
variable {X Y X' Y' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']
variable [Module.Flat S S']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FlatBC_subEquiv_one_tmul_19804f52a53f (E : S' ⊗[S] X ≃ₗ[S'] X') (D : Submodule S X) (D' : Submodule S' X')
    (h₁ : ∀ x ∈ D, E (1 ⊗ₜ x) ∈ D')
    (h₂ : D' ≤ Submodule.span S' ((fun x => E (1 ⊗ₜ x)) '' (D : Set X))) (x : D) :
    (subEquiv E D D' h₁ h₂ (1 ⊗ₜ x) : X') = E (1 ⊗ₜ (x : X)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FlatBC».«subEquiv_one_tmul» := P2M_GroundTheory_Heights__Heights_Kleiman_FlatBC_subEquiv_one_tmul_19804f52a53f
