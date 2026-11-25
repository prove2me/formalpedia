-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_BCMult_analyticResolution_hypotheses_projectiveLine_c81c7e631076
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_BCMult_analyticResolution_hypotheses_projectiveLine_c81c7e631076
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:41:16.277725+00:00
-- url     : https://prove2.me/theorems/d4f95e4d-2c6f-5a00-b983-03206e643728
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter BCMult analytic Resolution hypotheses projective Line c81c7e631076: P2 M Ground Theory Heights  Heights Indefinite Row Side Ful
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter BCMult analytic Resolution hypotheses projective Line c81c7e631076 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter BCMult analytic Resolution hypotheses projective Line c81c7e631076 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L668-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L668-L673

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_BCMult_analyticResolution_hypotheses_projectiveLine_c81c7e631076 :
    IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) (0 + 1) ∧ IsMultiHomog (Xj (R := ℚ) 0) (fun _ => 1) ∧
    Xj 0 ∉ (⊥ : Ideal (MRing ι1 ℚ)) ∧ ptI 0 ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 0) ∧
    ptI (R := ℂ) 0 ∈ (extC (ptI (R := ℚ) 0)).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«BCMult».«analyticResolution_hypotheses_projectiveLine» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_BCMult_analyticResolution_hypotheses_projectiveLine_c81c7e631076
