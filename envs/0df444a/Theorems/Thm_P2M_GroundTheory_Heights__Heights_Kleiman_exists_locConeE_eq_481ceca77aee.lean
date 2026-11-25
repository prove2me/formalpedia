-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_locConeE_eq_481ceca77aee
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_locConeE_eq_481ceca77aee
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:07.634409+00:00
-- url     : https://prove2.me/theorems/8ba82da6-4730-5aab-9d61-22f245bc7866
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists loc Cone E eq 481ceca77aee: P2 M Ground Theory Heights  Heights Kleiman exists loc Cone E eq 481ceca77aee
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists loc Cone E eq 481ceca77aee construction uses the P2 M Ground Theory Heights  Heights Kleiman exists loc Cone E eq 481ceca77aee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L133-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L133-L149

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_locConeE_eq_481ceca77aee (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : E}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGradedE c I, locConeE M I.1 hI z = singleE S x E c y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_locConeE_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_locConeE_eq_481ceca77aee
