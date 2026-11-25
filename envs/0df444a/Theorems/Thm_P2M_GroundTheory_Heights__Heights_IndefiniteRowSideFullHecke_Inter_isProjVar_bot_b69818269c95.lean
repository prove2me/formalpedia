-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_bot_b69818269c95
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_bot_b69818269c95
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:40:51.401714+00:00
-- url     : https://prove2.me/theorems/25bf8088-89f8-4408-8928-a972e61be9c3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var bot b69818269c95: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var bot b6981826
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var bot b69818269c95 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Proj Var bot b69818269c95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L337-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L337-L338

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_bot_b69818269c95 : IsProjVar (⊥ : Ideal (MRing ι1 ℂ)) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isProjVar_bot» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isProjVar_bot_b69818269c95
