-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_mul_89536a09261f
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_mul_89536a09261f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:20.527619+00:00
-- url     : https://prove2.me/theorems/07e2b05f-e65b-4fd2-ae6f-1b17885eac0b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under mul 89536a09261f: P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under mul 89536a09261f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under mul 89536a09261f construction uses the P2 M Ground Theory Heights  Heights Chart Energy Invariance invariant Under mul 89536a09261f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyInvariant.lean#L34-L37

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_mul_89536a09261f {A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hA : EnergyInvariantUnder A)
    (hB : EnergyInvariantUnder B) (hAdet : A.det ≠ 0) : EnergyInvariantUnder (A * B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyInvariance».«invariantUnder_mul» := P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_mul_89536a09261f
