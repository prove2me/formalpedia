-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_injective_e55cadb52ac8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_injective_e55cadb52ac8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:51.702597+00:00
-- url     : https://prove2.me/theorems/b568ffd3-8551-462d-a7b0-3c1a872dd40b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone E injective e55cadb52ac8: P2 M Ground Theory Heights  Heights Kleiman loc Cone E injective e55cadb52ac8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone E injective e55cadb52ac8 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone E injective e55cadb52ac8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L48-L57

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_injective_e55cadb52ac8 (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locConeE M I hI) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locConeE_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_injective_e55cadb52ac8
