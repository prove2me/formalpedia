-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_varMono_notMem_d447ddc5e348
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_varMono_notMem_d447ddc5e348
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:36.09995+00:00
-- url     : https://prove2.me/theorems/b2a12070-c270-42da-bf94-d94d336ef090
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds var Mono not Mem d447ddc5e348: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds var Mono not Mem d447ddc5e348
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds var Mono not Mem d447ddc5e348 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds var Mono not Mem d447ddc5e348 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L46-L50

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_varMono_notMem_d447ddc5e348 {I : Ideal (MRing ι)} [I.IsPrime] {v : ∀ k, ι k}
    (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ I) (e : K →₀ ℕ) : varMono v e ∉ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«varMono_notMem» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_varMono_notMem_d447ddc5e348
