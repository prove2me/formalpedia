-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_arInt_congr_e67f32b801d7
-- name    : P2M_GroundTheory_Heights__Heights_arInt_congr_e67f32b801d7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:11:15.497303+00:00
-- url     : https://prove2.me/theorems/984c15ef-9d35-4800-87cf-5b54d5b7a50a
-- title:
--   P2 M Ground Theory Heights  Heights ar Int congr e67f32b801d7: P2 M Ground Theory Heights  Heights ar Int congr e67f32b801d7
-- statement:
--   The P2 M Ground Theory Heights  Heights ar Int congr e67f32b801d7 construction uses the P2 M Ground Theory Heights  Heights ar Int congr e67f32b801d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L256-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L256-L260

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
omit [∀ k, Fintype (κ k)]

theorem P2M_GroundTheory_Heights__Heights_arInt_congr_e67f32b801d7 (P : Ideal (Geo.MRing κ)) (s : Geo.MRing κ) {e : ℕ}
    (L : Fin e → Geo.HermLine κ) {A A' : Geo.HermLine κ}
    (hh : ∀ z ∈ Geo.mcPts P, A.h z = A'.h z) : Geo.arInt P s A L = Geo.arInt P s A' L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«arInt_congr» := P2M_GroundTheory_Heights__Heights_arInt_congr_e67f32b801d7
