-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_oldCoord_injective_8ba726ea0c16
-- name    : P2M_GroundTheory_Heights__Heights_SectionCycle_oldCoord_injective_8ba726ea0c16
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:19.600271+00:00
-- url     : https://prove2.me/theorems/78d02a4d-c290-5bec-acf5-8e6f501d6dfe
-- title:
--   P2 M Ground Theory Heights  Heights Section Cycle old Coord injective 8ba726ea0c16: P2 M Ground Theory Heights  Heights Section Cycle old Coord injective 8ba726ea0c16
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Cycle old Coord injective 8ba726ea0c16 construction uses the P2 M Ground Theory Heights  Heights Section Cycle old Coord injective 8ba726ea0c16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/LiftOldChartMonomialMemPrimeCompl.lean#L140-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_SectionCycle_oldCoord_injective_8ba726ea0c16 : Function.Injective D.oldCoord := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionCycle».«oldCoord_injective» := P2M_GroundTheory_Heights__Heights_SectionCycle_oldCoord_injective_8ba726ea0c16
