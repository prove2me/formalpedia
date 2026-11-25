-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothMetric_of_isSmoothHerm_ffcf1c51959d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothMetric_of_isSmoothHerm_ffcf1c51959d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:01:19.712159+00:00
-- url     : https://prove2.me/theorems/aac5a34d-27e9-4568-b756-2c13a16e2154
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Metric of is Smooth Herm ffcf1c51959d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sm
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Metric of is Smooth Herm ffcf1c51959d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Metric of is Smooth Herm ffcf1c51959d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothMetricOfIsSmoothHerm.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothMetricOfIsSmoothHerm.lean#L37-L41

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothMetric_of_isSmoothHerm_ffcf1c51959d (P : Ideal (MRing ι ℂ)) (L : HLine ι)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm L) : IsSmoothMetric P L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isSmoothMetric_of_isSmoothHerm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothMetric_of_isSmoothHerm_ffcf1c51959d
