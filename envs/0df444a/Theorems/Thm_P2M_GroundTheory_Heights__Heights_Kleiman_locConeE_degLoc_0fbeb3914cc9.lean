-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_degLoc_0fbeb3914cc9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_degLoc_0fbeb3914cc9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:55.482366+00:00
-- url     : https://prove2.me/theorems/1cf2a0f5-307e-54ef-bcb3-bfaed49d5b0d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone E deg Loc 0fbeb3914cc9: P2 M Ground Theory Heights  Heights Kleiman loc Cone E deg Loc 0fbeb3914cc9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone E deg Loc 0fbeb3914cc9 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone E deg Loc 0fbeb3914cc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L82-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
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
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_degLoc_0fbeb3914cc9 (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSubE I.1}
    (hz : z ∈ degLoc M.coneGradedE c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locConeE M I.1 hI z = singleE S x E c v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locConeE_degLoc» := P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_degLoc_0fbeb3914cc9
