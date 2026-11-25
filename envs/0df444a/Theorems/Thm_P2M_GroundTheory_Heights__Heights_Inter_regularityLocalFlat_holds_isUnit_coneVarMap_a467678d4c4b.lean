-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_coneVarMap_a467678d4c4b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_coneVarMap_a467678d4c4b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:04.965362+00:00
-- url     : https://prove2.me/theorems/905cdbc6-1756-4632-be4b-9079f7c35621
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit cone Var Map a467678d4c4b: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit cone Var Map a467
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit cone Var Map a467678d4c4b construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Unit cone Var Map a467678d4c4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L156-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L156-L169

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_coneVarMap_a467678d4c4b (hPW : P ≤ W) (hWh : IsMultiHomogIdeal W) {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) (G : MvPolynomial K (locRing P W)) {e : K →₀ ℕ}
    (he : IsUnit (coeff e G)) : IsUnit (coneVarMap P W hPW v G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«isUnit_coneVarMap» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_coneVarMap_a467678d4c4b
