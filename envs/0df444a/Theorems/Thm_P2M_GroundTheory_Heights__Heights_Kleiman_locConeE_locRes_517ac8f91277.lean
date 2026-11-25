-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_locRes_517ac8f91277
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_locRes_517ac8f91277
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:59.313848+00:00
-- url     : https://prove2.me/theorems/de0ebab2-ddf4-4107-b0e0-156688a49470
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone E loc Res 517ac8f91277: P2 M Ground Theory Heights  Heights Kleiman loc Cone E loc Res 517ac8f91277
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone E loc Res 517ac8f91277 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone E loc Res 517ac8f91277 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L59-L66

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_locRes_517ac8f91277 {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSubE I) :
    locConeE M J hJ (locRes h z) = locConeE M I (h.trans hJ) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locConeE_locRes» := P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_locRes_517ac8f91277
