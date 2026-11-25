-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_clear_mem_f30bf8927550
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_clear_mem_f30bf8927550
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:44.32449+00:00
-- url     : https://prove2.me/theorems/f4cdc677-4346-4679-aebe-20cb88b4766c
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of clear mem f30bf8927550: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of clear mem f30bf8927550
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of clear mem f30bf8927550 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds mem of clear mem f30bf8927550 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L110-L118

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_clear_mem_f30bf8927550 {I : Ideal (MRing ι)} [I.IsPrime] (hI : IsMultiHomogIdeal I) {v : ∀ k, ι k}
    (hvI : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ I) (s : Finset (K →₀ ℕ)) {b : K → ℕ} {N : (K →₀ ℕ) → MRing ι}
    (hN : ∀ e, IsMultiHomog (N e) b) (h : ∑ e ∈ s, N e * varMono v e ∈ I) : ∀ e ∈ s, N e ∈ I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«mem_of_clear_mem» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_clear_mem_f30bf8927550
