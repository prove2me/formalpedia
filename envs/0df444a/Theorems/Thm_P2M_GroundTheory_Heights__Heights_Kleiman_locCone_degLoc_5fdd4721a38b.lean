-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_degLoc_5fdd4721a38b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locCone_degLoc_5fdd4721a38b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:02.914506+00:00
-- url     : https://prove2.me/theorems/78eddf66-0bb2-41db-a068-165c2b8242a9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone deg Loc 5fdd4721a38b: P2 M Ground Theory Heights  Heights Kleiman loc Cone deg Loc 5fdd4721a38b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone deg Loc 5fdd4721a38b construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone deg Loc 5fdd4721a38b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L96-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L96-L112

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locCone_degLoc_5fdd4721a38b (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSub I.1}
    (hz : z ∈ degLoc M.coneGraded c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locCone M I.1 hI z = coneSingle S x c v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locCone_degLoc» := P2M_GroundTheory_Heights__Heights_Kleiman_locCone_degLoc_5fdd4721a38b
