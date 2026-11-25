-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ChartDehomIdeal_proof_1927dc9452ac
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ChartDehomIdeal_proof_1927dc9452ac
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:58.700055+00:00
-- url     : https://prove2.me/theorems/f273897c-6d60-5e2b-ad37-5fae332cd260
-- title:
--   P2 M Ground Theory Heights  Heights Targets Chart Dehom Ideal proof 1927dc9452ac: P2 M Ground Theory Heights  Heights Targets Chart Dehom Ideal proof 1927dc9452ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Chart Dehom Ideal proof 1927dc9452ac construction uses the P2 M Ground Theory Heights  Heights Targets Chart Dehom Ideal proof 1927dc9452ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDehomIdeal.lean#L14-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDehomIdeal.lean#L14-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartDehomIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_proof_17ca30ede7f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartSet chartLift segre_chartLift chartLift_segre_apply)

theorem P2M_GroundTheory_Heights__Heights_Targets_ChartDehomIdeal_proof_1927dc9452ac : ChartDehomIdeal.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ChartDehomIdeal».«proof» := P2M_GroundTheory_Heights__Heights_Targets_ChartDehomIdeal_proof_1927dc9452ac
