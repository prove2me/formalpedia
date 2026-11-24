-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_realCLE_apply_c180c099b79c
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_realCLE_apply_c180c099b79c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:20.669107+00:00
-- url     : https://prove2.me/theorems/b81b9f19-f7f2-446e-9c0e-874de87d0092
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance real CLE apply c180c099b79c: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance real CLE apply c180c099b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance real CLE apply c180c099b79c construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance real CLE apply c180c099b79c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L103-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_realCLE_apply_c180c099b79c (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (y : Fin D → ℂ) :
    realCLE P hP y = P *ᵥ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«realCLE_apply» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_realCLE_apply_c180c099b79c
