-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothFn_projLineRatio_45f616a3bbbb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothFn_projLineRatio_45f616a3bbbb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:38:55.465407+00:00
-- url     : https://prove2.me/theorems/97a42850-fd73-4ead-adcb-cd67c726ecb9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Fn proj Line Ratio 45f616a3bbbb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth F
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Fn proj Line Ratio 45f616a3bbbb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Smooth Fn proj Line Ratio 45f616a3bbbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L527-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L527-L530

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothFn_projLineRatio_45f616a3bbbb (P : Ideal (MRing ι1 ℂ)) (j : Fin 2) : IsSmoothFn P (projectiveLineCoordinates j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isSmoothFn_projLineRatio» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothFn_projLineRatio_45f616a3bbbb
