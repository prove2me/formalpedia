-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothPot_of_fn_8b2379f23a35
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothPot_of_fn_8b2379f23a35
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:40:38.20749+00:00
-- url     : https://prove2.me/theorems/eb1931c4-cf76-4239-b0a4-db5a15968130
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Pot of fn 8b2379f23a35: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Pot of fn
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Pot of fn 8b2379f23a35 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Pot of fn 8b2379f23a35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L544-L547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L544-L547

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineHomogeneousLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
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
open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothPot_of_fn_8b2379f23a35 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι ℂ)} {g : MCone ι → ℝ} (h : IsSmoothFn P g) :
    IsSmoothPot P g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isSmoothPot_of_fn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothPot_of_fn_8b2379f23a35
