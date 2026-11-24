-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_of_row_zero_4634931e014b
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_of_row_zero_4634931e014b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:32.85714+00:00
-- url     : https://prove2.me/theorems/408b9f7d-46f2-4c57-bc7a-dacb94dd1a2f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det of row zero 4634931e014b: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det of row zero 4634931e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det of row zero 4634931e014b construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det of row zero 4634931e014b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartMassInvariant.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
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
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_of_row_zero_4634931e014b (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0) :
    T.det = T 0 0 * (T.submatrix Fin.succ Fin.succ).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«det_of_row_zero» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_of_row_zero_4634931e014b
