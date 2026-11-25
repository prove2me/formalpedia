-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointVertRAux_degC_eq_finrank_02d1f9d69ae7
-- name    : P2M_GroundTheory_Heights__Heights_PointVertRAux_degC_eq_finrank_02d1f9d69ae7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:31.37397+00:00
-- url     : https://prove2.me/theorems/c8df6df4-4df6-4298-a5f1-1f3abe56153f
-- title:
--   P2 M Ground Theory Heights  Heights Point Vert RAux deg C eq finrank 02d1f9d69ae7: P2 M Ground Theory Heights  Heights Point Vert RAux deg C eq finrank 02d1f9d69ae7
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Vert RAux deg C eq finrank 02d1f9d69ae7 construction uses the P2 M Ground Theory Heights  Heights Point Vert RAux deg C eq finrank 02d1f9d69ae7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointVertR.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointVertR.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointVertR
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.PointVertRAux

theorem P2M_GroundTheory_Heights__Heights_PointVertRAux_degC_eq_finrank_02d1f9d69ae7 {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Module.finrank ℚ (blockFnField y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointVertRAux».«degC_eq_finrank» := P2M_GroundTheory_Heights__Heights_PointVertRAux_degC_eq_finrank_02d1f9d69ae7
