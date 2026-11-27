-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongLimitAtBranches_proof_fac54619724b
-- name    : P2M_GroundTheory_Heights__Heights_LelongLimitAtBranches_proof_fac54619724b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:12.359257+00:00
-- url     : https://prove2.me/theorems/44767221-4bd2-46d7-bc46-b6303d856b05
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Limit At Branches proof fac54619724b: P2 M Ground Theory Heights  Heights Lelong Limit At Branches proof fac54619724b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Limit At Branches proof fac54619724b construction uses the P2 M Ground Theory Heights  Heights Lelong Limit At Branches proof fac54619724b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitAtBranches.lean#L15-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongLimitAtBranches.lean#L15-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitAtBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchIntDecompose
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBranchInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolydiscLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitAtBranches
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_LelongLimitAtBranches_proof_fac54619724b (hDec : BranchIntDecompose.Statement) (hSl : SliceBranchInt.Statement)
    (hLim : PolydiscLelongLimit.Statement) (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) :
    LelongLimitAtBranches.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongLimitAtBranches».«proof» := P2M_GroundTheory_Heights__Heights_LelongLimitAtBranches_proof_fac54619724b
