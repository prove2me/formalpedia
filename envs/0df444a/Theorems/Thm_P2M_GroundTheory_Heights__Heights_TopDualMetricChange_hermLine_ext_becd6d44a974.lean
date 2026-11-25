-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TopDualMetricChange_hermLine_ext_becd6d44a974
-- name    : P2M_GroundTheory_Heights__Heights_TopDualMetricChange_hermLine_ext_becd6d44a974
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:46.744803+00:00
-- url     : https://prove2.me/theorems/40cade6d-3e9f-5da6-b148-82e303e3a32e
-- title:
--   P2 M Ground Theory Heights  Heights Top Dual Metric Change herm Line ext becd6d44a974: P2 M Ground Theory Heights  Heights Top Dual Metric Change herm Line ext becd6d44a974
-- statement:
--   The P2 M Ground Theory Heights  Heights Top Dual Metric Change herm Line ext becd6d44a974 construction uses the P2 M Ground Theory Heights  Heights Top Dual Metric Change herm Line ext becd6d44a974 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopMetricChange.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopMetricChange
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.TopDualMetricChange
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_TopDualMetricChange_hermLine_ext_becd6d44a974 {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TopDualMetricChange».«hermLine_ext» := P2M_GroundTheory_Heights__Heights_TopDualMetricChange_hermLine_ext_becd6d44a974
