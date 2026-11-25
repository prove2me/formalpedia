-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorBranches_proof_dd697b6c910b
-- name    : P2M_GroundTheory_Heights__Heights_DivisorBranches_proof_dd697b6c910b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:12:17.038194+00:00
-- url     : https://prove2.me/theorems/ae333969-a5bb-4d5c-8c71-8e070418ea41
-- title:
--   P2 M Ground Theory Heights  Heights Divisor Branches proof dd697b6c910b: P2 M Ground Theory Heights  Heights Divisor Branches proof dd697b6c910b
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor Branches proof dd697b6c910b construction uses the P2 M Ground Theory Heights  Heights Divisor Branches proof dd697b6c910b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorBranches.lean#L39-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorBranches.lean#L39-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorRegularGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPointBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorBranches
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
open MvPolynomial Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorBranches

theorem P2M_GroundTheory_Heights__Heights_DivisorBranches_proof_dd697b6c910b (hModel : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement)
    (hReg : DivisorRegularGeneric.Statement) (hChart : NormalDivisorChartGeneric.Statement)
    (hDouble : NormalDoublePointsGeneric.Statement) (hGood : DivisorGoodPointBranches.Statement) :
    DivisorBranches.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorBranches».«proof» := P2M_GroundTheory_Heights__Heights_DivisorBranches_proof_dd697b6c910b
