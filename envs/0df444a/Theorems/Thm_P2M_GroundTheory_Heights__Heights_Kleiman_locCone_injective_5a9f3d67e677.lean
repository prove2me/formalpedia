-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_injective_5a9f3d67e677
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locCone_injective_5a9f3d67e677
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:50:20.407415+00:00
-- url     : https://prove2.me/theorems/c032b58d-0f69-4a1b-9ee3-9a0603180d3f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone injective 5a9f3d67e677: P2 M Ground Theory Heights  Heights Kleiman loc Cone injective 5a9f3d67e677
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone injective 5a9f3d67e677 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone injective 5a9f3d67e677 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L62-L71

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locCone_injective_5a9f3d67e677 (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locCone M I hI) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locCone_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_locCone_injective_5a9f3d67e677
