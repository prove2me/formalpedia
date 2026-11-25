-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_isRadical_616121f2ccad
-- name    : P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_isRadical_616121f2ccad
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:09.449855+00:00
-- url     : https://prove2.me/theorems/873c6d1e-941b-432e-a90d-52c61bd2c447
-- title:
--   P2 M Ground Theory Heights  Heights Targets segre Chart Ideal is Radical 616121f2ccad: P2 M Ground Theory Heights  Heights Targets segre Chart Ideal is Radical 616121f2ccad
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets segre Chart Ideal is Radical 616121f2ccad construction uses the P2 M Ground Theory Heights  Heights Targets segre Chart Ideal is Radical 616121f2ccad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDivisorLength.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDivisorLength.lean#L18-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSectionLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPiQuotCokerFiniteLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartDivisorLength
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

theorem P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_isRadical_616121f2ccad (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    (segreChartIdeal P σ i).IsRadical := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«segreChartIdeal_isRadical» := P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_isRadical_616121f2ccad
