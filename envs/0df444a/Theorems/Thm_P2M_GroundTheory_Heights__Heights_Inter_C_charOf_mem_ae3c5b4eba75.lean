-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_C_charOf_mem_ae3c5b4eba75
-- name    : P2M_GroundTheory_Heights__Heights_Inter_C_charOf_mem_ae3c5b4eba75
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:52.693962+00:00
-- url     : https://prove2.me/theorems/a65baebd-983b-5820-aed2-d00f31355d22
-- title:
--   P2 M Ground Theory Heights  Heights Inter C char Of mem ae3c5b4eba75: P2 M Ground Theory Heights  Heights Inter C char Of mem ae3c5b4eba75
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter C char Of mem ae3c5b4eba75 construction uses the P2 M Ground Theory Heights  Heights Inter C char Of mem ae3c5b4eba75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PGeoNumCut.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PGeoNumCut.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PGeoNumCut
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
open MvPolynomial GroundTheory.Heights₂.Heights.Bridge GroundTheory.Heights₂.Heights.Bridge.GeoNum
  GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_C_charOf_mem_ae3c5b4eba75 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«C_charOf_mem» := P2M_GroundTheory_Heights__Heights_Inter_C_charOf_mem_ae3c5b4eba75
