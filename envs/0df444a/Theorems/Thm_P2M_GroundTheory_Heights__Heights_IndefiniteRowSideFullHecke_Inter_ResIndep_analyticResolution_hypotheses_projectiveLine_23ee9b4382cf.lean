-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ResIndep_analyticResolution_hypotheses_projectiveLine_23ee9b4382cf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ResIndep_analyticResolution_hypotheses_projectiveLine_23ee9b4382cf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:51:27.124409+00:00
-- url     : https://prove2.me/theorems/f81bed31-0e27-4f06-9a8c-8114e305a329
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res Indep analytic Resolution hypotheses projective Line 23ee9b4382cf: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res Indep analytic Resolution hypotheses projective Line 23ee9b4382cf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Res Indep analytic Resolution hypotheses projective Line 23ee9b4382cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L602-L607
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L602-L607

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ResIndep_analyticResolution_hypotheses_projectiveLine_23ee9b4382cf :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 ∧ (∀ j, IsSmoothPot ⊥ ((![logH fubiniStudyLine] : Fin 1 → _) j)) ∧
    (IsSmoothFn ⊥ (secNorm fubiniStudyLine (Xj 0)) ∨ ∃ (A : HLine ι1) (s : MRing ι1 ℂ),
      IsSmoothMetric ⊥ A ∧ IsFormSec ⊥ A s ∧ secNorm fubiniStudyLine (Xj 0) = secNorm A s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«ResIndep».«analyticResolution_hypotheses_projectiveLine» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ResIndep_analyticResolution_hypotheses_projectiveLine_23ee9b4382cf
