-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isLocalization_coneVarMap_9d3466758b52
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isLocalization_coneVarMap_9d3466758b52
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:20.739915+00:00
-- url     : https://prove2.me/theorems/51ab86f7-e7de-4b82-898c-22617a3d4320
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Localization cone Var Map 9d3466758b52: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Localization c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Localization cone Var Map 9d3466758b52 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds is Localization cone Var Map 9d3466758b52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L234-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L234-L266

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isLocalization_coneVarMap_9d3466758b52 (hPW : P ≤ W) (hPh : IsMultiHomogIdeal P) (hWh : IsMultiHomogIdeal W)
    (v : ∀ k, ι k) (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) :
    haveI := isLocalRing hPW
    letI := (coneVarMap P W hPW v).toRingHom.toAlgebra
    haveI := isPrime_map_C K (maximalIdeal (locRing P W))
    IsLocalization ((maximalIdeal (locRing P W)).map
      (C : locRing P W →+* MvPolynomial K (locRing P W))).primeCompl (coneLocRing P W hPW) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«isLocalization_coneVarMap» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isLocalization_coneVarMap_9d3466758b52
