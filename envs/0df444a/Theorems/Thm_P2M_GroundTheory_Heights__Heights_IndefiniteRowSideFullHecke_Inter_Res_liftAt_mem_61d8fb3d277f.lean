-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_liftAt_mem_61d8fb3d277f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_liftAt_mem_61d8fb3d277f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:18.299525+00:00
-- url     : https://prove2.me/theorems/882c950c-6cd8-40b7-8c59-14a1fd2dc411
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res lift At mem 61d8fb3d277f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res lift At mem 61d8fb3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res lift At mem 61d8fb3d277f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res lift At mem 61d8fb3d277f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean#L73-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
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
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_liftAt_mem_61d8fb3d277f {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) : R.liftAt x y ∈ zPts P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«Res».«liftAt_mem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_liftAt_mem_61d8fb3d277f
