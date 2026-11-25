-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_algebraMap_cone_a38ac8eb988f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_algebraMap_cone_a38ac8eb988f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:41.82357+00:00
-- url     : https://prove2.me/theorems/e1b68971-ea42-4fa3-b76e-d319722fb470
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit algebra Map cone a38ac8eb988f: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit algebra Map c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit algebra Map cone a38ac8eb988f construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit algebra Map cone a38ac8eb988f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L149-L152

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_algebraMap_cone_a38ac8eb988f (hPW : P ≤ W) {g : MRing ι} (hg : g ∉ W) :
    IsUnit (algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«isUnit_algebraMap_cone» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_algebraMap_cone_a38ac8eb988f
