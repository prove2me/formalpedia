-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mixedDisc_mul_mul_6e0de3118a6e
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mixedDisc_mul_mul_6e0de3118a6e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:18.685859+00:00
-- url     : https://prove2.me/theorems/73b06344-5f80-46b6-bf60-9ae1f9bae3fc
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mixed Disc mul mul 6e0de3118a6e: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mixed Disc mul mul 6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mixed Disc mul mul 6e0de3118a6e construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance mixed Disc mul mul 6e0de3118a6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L146-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L146-L153

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mixedDisc_mul_mul_6e0de3118a6e (P Q : Matrix (Fin D) (Fin D) ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => P * A k * Q) = P.det * Q.det * mixedDisc A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«mixedDisc_mul_mul» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_mixedDisc_mul_mul_6e0de3118a6e
