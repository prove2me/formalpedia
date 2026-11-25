-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locModE_subsingleton_579608ddf9fc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locModE_subsingleton_579608ddf9fc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:41.811947+00:00
-- url     : https://prove2.me/theorems/169185a5-eb16-459b-a394-b1c296fb01db
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Mod E subsingleton 579608ddf9fc: P2 M Ground Theory Heights  Heights Kleiman loc Mod E subsingleton 579608ddf9fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Mod E subsingleton 579608ddf9fc construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Mod E subsingleton 579608ddf9fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L68-L80

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locModE_subsingleton_579608ddf9fc {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod S N M.coneSubE I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locModE_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_locModE_subsingleton_579608ddf9fc
