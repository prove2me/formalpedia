-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_mono_2ffebf068faf
-- name    : P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_mono_2ffebf068faf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:29.805937+00:00
-- url     : https://prove2.me/theorems/47c4d0c9-b396-5af2-8f2c-41bed8afbe73
-- title:
--   P2 M Ground Theory Heights  Heights Targets segre Chart Ideal mono 2ffebf068faf: P2 M Ground Theory Heights  Heights Targets segre Chart Ideal mono 2ffebf068faf
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets segre Chart Ideal mono 2ffebf068faf construction uses the P2 M Ground Theory Heights  Heights Targets segre Chart Ideal mono 2ffebf068faf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDivisorLength.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDivisorLength.lean#L27-L31

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

theorem P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_mono_2ffebf068faf {P W : Ideal (MRing ι)} (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : segreChartIdeal P σ i ≤ segreChartIdeal W σ i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«segreChartIdeal_mono» := P2M_GroundTheory_Heights__Heights_Targets_segreChartIdeal_mono_2ffebf068faf
