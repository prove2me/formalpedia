-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_mul_right_3611512dcdae
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_mul_right_3611512dcdae
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:16.604852+00:00
-- url     : https://prove2.me/theorems/ebda1fad-d656-4460-9854-f477eda09ddd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of mul right 3611512dcdae: P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of mul right 3611512d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of mul right 3611512dcdae construction uses the P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under of mul right 3611512dcdae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L39-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyInvariance
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_mul_right_3611512dcdae {C V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hCV : EnergyInvariantUnder (C * V)) (hV : EnergyInvariantUnder V) (hC : C.det ≠ 0) :
    EnergyInvariantUnder C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyInvariance».«invariantUnder_of_mul_right» := P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_mul_right_3611512dcdae
