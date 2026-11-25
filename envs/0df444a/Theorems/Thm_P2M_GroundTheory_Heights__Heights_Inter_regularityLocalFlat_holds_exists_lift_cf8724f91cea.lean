-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_lift_cf8724f91cea
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_lift_cf8724f91cea
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:18.37623+00:00
-- url     : https://prove2.me/theorems/d7da6e45-5fde-4082-902e-b4c89fbd1888
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists lift cf8724f91cea: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists lift cf8724f91cea
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists lift cf8724f91cea construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds exists lift cf8724f91cea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L173-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L173-L201

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
variable {P W}

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_lift_cf8724f91cea (hPW : P ≤ W) {v : ∀ k, ι k} (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) (f : MRing ι) :
    ∃ F, coneVarMap P W hPW v F =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«exists_lift» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_lift_cf8724f91cea
