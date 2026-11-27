-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projectiveLineZeroForm_holds_analyticResolution_hypotheses_projectiveLine_85ec5da3cef9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projectiveLineZeroForm_holds_analyticResolution_hypotheses_projectiveLine_85ec5da3cef9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:40:52.550683+00:00
-- url     : https://prove2.me/theorems/c25e9ca7-e42f-4170-a543-21d61895a25b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter projective Line Zero Form holds analytic Resolution hypotheses projective Line 85ec5da3cef9: P2 M Ground Theory Heights  Height
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter projective Line Zero Form holds analytic Resolution hypotheses projective Line 85ec5da3cef9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter projective Line Zero Form holds analytic Resolution hypotheses projective Line 85ec5da3cef9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L589-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean#L589-L600

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projectiveLineZeroForm_holds_analyticResolution_hypotheses_projectiveLine_85ec5da3cef9 :
    IsPotential ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ∧
    IsSection ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ReciprocityTheory.AnForm.M.projectiveLinePairSection ∧
    IsSNC ReciprocityTheory.AnForm.M.p1 ReciprocityTheory.AnForm.M.fsPot ReciprocityTheory.AnForm.M.projectiveLinePairSection ![1]
      ![({OnePoint.infty} : Set (OnePoint ℂ))] ∧
    HoloMap (ReciprocityTheory.AnForm.M.ptAtlas ({OnePoint.infty} : Set (OnePoint ℂ))) ReciprocityTheory.AnForm.M.p1
      Subtype.val ∧
    ReciprocityTheory.AnForm.M.p1.Smooth ReciprocityTheory.AnForm.M.fsH ∧
    ∀ i : Fin 0, IsPotential ReciprocityTheory.AnForm.M.p1 ((Fin.elim0 : Fin 0 → LocPot (OnePoint ℂ)) i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«projectiveLineZeroForm_holds».«analyticResolution_hypotheses_projectiveLine» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projectiveLineZeroForm_holds_analyticResolution_hypotheses_projectiveLine_85ec5da3cef9
