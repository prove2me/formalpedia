-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjectivePlaneOverRationals_analyticResolution_hypotheses_projectiveLine_88afe0f39a13
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjectivePlaneOverRationals_analyticResolution_hypotheses_projectiveLine_88afe0f39a13
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:40:52.209614+00:00
-- url     : https://prove2.me/theorems/f56de47f-d58b-4c6f-87bf-34f5aa2abf5e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Projective Plane Over Rationals analytic Resolution hypotheses projective Line 88afe0f39a13: P2 M Ground Theory Heights  Height
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Projective Plane Over Rationals analytic Resolution hypotheses projective Line 88afe0f39a13 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Projective Plane Over Rationals analytic Resolution hypotheses projective Line 88afe0f39a13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L715-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L715-L727

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjectivePlaneOverRationals_analyticResolution_hypotheses_projectiveLine_88afe0f39a13 :
    IsProjVarQ (⊥ : Ideal (MRing ι1 ℚ)) (0 + 1) ∧
    (∀ Z ∈ (extC (⊥ : Ideal (MRing ι1 ℚ))).minimalPrimes, Nonempty (Res ι1 Z (0 + 1))) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 0), ∀ Z ∈ (extC W).minimalPrimes,
      Nonempty (Res ι1 Z 0)) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 1), ∀ Z ∈ (extC W).minimalPrimes,
      Nonempty (Res ι1 Z 0)) ∧
    (∀ j, IsSmoothMetric (extC ⊥) ((![] : Fin 0 → HLine ι1) j)) ∧ IsSmoothMetric (extC ⊥) fubiniStudyLine ∧
    IsSmoothMetric (extC ⊥) fubiniStudyLine ∧ IsFormSec (⊥ : Ideal (MRing ι1 ℚ)) fubiniStudyLine (Xj 0) ∧
    IsFormSec (⊥ : Ideal (MRing ι1 ℚ)) fubiniStudyLine (Xj 1) ∧
    (∀ W ∈ comps (⊥ : Ideal (MRing ι1 ℚ)) (Xj 0), W ∉ comps ⊥ (Xj 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«ProjectivePlaneOverRationals».«analyticResolution_hypotheses_projectiveLine» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjectivePlaneOverRationals_analyticResolution_hypotheses_projectiveLine_88afe0f39a13
