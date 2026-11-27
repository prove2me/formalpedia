-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_proof_b8227cd2a891
-- name    : P2M_GroundTheory_Heights__Heights_RatChartChangeVar_proof_b8227cd2a891
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:36.316587+00:00
-- url     : https://prove2.me/theorems/3fcf69ff-6b0a-51b4-a033-fe2888a426de
-- title:
--   P2 M Ground Theory Heights  Heights Rat Chart Change Var proof b8227cd2a891: P2 M Ground Theory Heights  Heights Rat Chart Change Var proof b8227cd2a891
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Chart Change Var proof b8227cd2a891 construction uses the P2 M Ground Theory Heights  Heights Rat Chart Change Var proof b8227cd2a891 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L184-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatChartChangeVar.lean#L184-L198

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_proof_4b5bf5e5d261
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PosPartSplit_proof_e6248afef178
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets

theorem P2M_GroundTheory_Heights__Heights_RatChartChangeVar_proof_b8227cd2a891 (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement) :
    RatChartChangeVar.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatChartChangeVar».«proof» := P2M_GroundTheory_Heights__Heights_RatChartChangeVar_proof_b8227cd2a891
