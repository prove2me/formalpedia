-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ThreeSphereMass_analyticResolution_hypotheses_projectiveLine_7df64c983bed
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ThreeSphereMass_analyticResolution_hypotheses_projectiveLine_7df64c983bed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:39:49.043779+00:00
-- url     : https://prove2.me/theorems/d5946772-b3f1-4433-907c-28cfc5acedb4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Three Sphere Mass analytic Resolution hypotheses projective Line 7df64c983bed: P2 M Ground Theory Heights  Heights Indefinite R
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Three Sphere Mass analytic Resolution hypotheses projective Line 7df64c983bed construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Three Sphere Mass analytic Resolution hypotheses projective Line 7df64c983bed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L615-L621
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L615-L621

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ThreeSphereMass_analyticResolution_hypotheses_projectiveLine_7df64c983bed :
    IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 ∧ Nonempty (Res ι1 ⊥ 1) ∧
    (∀ j, IsSmoothMetric ⊥ ((![fubiniStudyLine] : Fin 1 → HLine ι1) j)) ∧
    (∀ j, IsSmoothMetric ⊥ ((![fsTw] : Fin 1 → HLine ι1) j)) ∧
    (∀ j, ((![fubiniStudyLine] : Fin 1 → HLine ι1) j).a = ((![fsTw] : Fin 1 → HLine ι1) j).a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«ThreeSphereMass».«analyticResolution_hypotheses_projectiveLine» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ThreeSphereMass_analyticResolution_hypotheses_projectiveLine_7df64c983bed
