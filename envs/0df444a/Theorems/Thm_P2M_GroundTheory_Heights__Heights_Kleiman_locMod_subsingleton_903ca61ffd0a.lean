-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMod_subsingleton_903ca61ffd0a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locMod_subsingleton_903ca61ffd0a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:54.825342+00:00
-- url     : https://prove2.me/theorems/89e04302-897d-4d9b-8834-f7ceb3e6e57d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Mod subsingleton 903ca61ffd0a: P2 M Ground Theory Heights  Heights Kleiman loc Mod subsingleton 903ca61ffd0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Mod subsingleton 903ca61ffd0a construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Mod subsingleton 903ca61ffd0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L82-L94

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locMod_subsingleton_903ca61ffd0a {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod S N M.coneSub I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locMod_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_locMod_subsingleton_903ca61ffd0a
