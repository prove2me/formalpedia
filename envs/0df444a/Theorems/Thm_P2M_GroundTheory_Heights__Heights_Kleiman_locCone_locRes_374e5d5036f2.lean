-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:23.460842+00:00
-- url     : https://prove2.me/theorems/cceb53db-8391-512b-8768-980b4b95cee6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone loc Res 374e5d5036f2: P2 M Ground Theory Heights  Heights Kleiman loc Cone loc Res 374e5d5036f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone loc Res 374e5d5036f2 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone loc Res 374e5d5036f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L73-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2 {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSub I) :
    locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locCone_locRes» := P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2
