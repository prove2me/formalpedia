-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_rat_complex_f9a682025ea3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_rat_complex_f9a682025ea3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:59:46.093277+00:00
-- url     : https://prove2.me/theorems/fec08364-16f4-5c71-9bf0-7980079c54db
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map rat complex f9a682025ea3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map rat complex f9a68202
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map rat complex f9a682025ea3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter map rat complex f9a682025ea3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothMetricOfIsSmoothHerm.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothMetricOfIsSmoothHerm.lean#L19-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_rat_complex_f9a682025ea3 (f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) :
    MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (Int.castRingHom ℚ) f) =
      MvPolynomial.map (Int.castRingHom ℂ) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«map_rat_complex» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_map_rat_complex_f9a682025ea3
