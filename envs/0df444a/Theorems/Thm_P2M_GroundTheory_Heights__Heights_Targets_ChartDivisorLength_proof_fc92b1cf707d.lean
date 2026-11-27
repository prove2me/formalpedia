-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ChartDivisorLength_proof_fc92b1cf707d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ChartDivisorLength_proof_fc92b1cf707d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:12.406963+00:00
-- url     : https://prove2.me/theorems/98178e19-3bf4-52e1-80cf-d22629f667c1
-- title:
--   P2 M Ground Theory Heights  Heights Targets Chart Divisor Length proof fc92b1cf707d: P2 M Ground Theory Heights  Heights Targets Chart Divisor Length proof fc92b1cf707d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Chart Divisor Length proof fc92b1cf707d construction uses the P2 M Ground Theory Heights  Heights Targets Chart Divisor Length proof fc92b1cf707d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDivisorLength.lean#L33-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDivisorLength.lean#L33-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSectionLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPiQuotCokerFiniteLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartDivisorLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalSectionLengthSum_proof_8da0748c6132
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_proof_a6f4aca3e046
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PiQuotCokerFiniteLength_proof_b5eb4358c6fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionLengthSum_proof_50fcfdf5037f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn divSupp IsHorizontal multAt mcPts)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents localMult mem_segreChartComponents)
variable {K : Type*} [Fintype K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_Targets_ChartDivisorLength_proof_fc92b1cf707d (hNotMem : ChartSectionNotMem.Statement) (hComp : ChartDivisorComponents.Statement)
    (hLen : ChartSectionLength.Statement) : ChartDivisorLength.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ChartDivisorLength».«proof» := P2M_GroundTheory_Heights__Heights_Targets_ChartDivisorLength_proof_fc92b1cf707d
