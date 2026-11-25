-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_det_cols_ee6747bf1c9a
-- name    : P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_det_cols_ee6747bf1c9a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:38.027935+00:00
-- url     : https://prove2.me/theorems/f219eba1-40f6-48a2-af98-0e58de2204b4
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Lattice Covolume det cols ee6747bf1c9a: P2 M Ground Theory Heights  Heights PGauss Lattice Covolume det cols ee6747bf1c9a
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Lattice Covolume det cols ee6747bf1c9a construction uses the P2 M Ground Theory Heights  Heights PGauss Lattice Covolume det cols ee6747bf1c9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCovolume.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCovolume.lean#L47-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeCovolume
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
open Matrix MeasureTheory Module
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussLatticeCovolume

theorem P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_det_cols_ee6747bf1c9a {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    (EuclideanSpace.basisFun (Fin g) ℝ).toBasis.det (cols B) = B.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussLatticeCovolume».«det_cols» := P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_det_cols_ee6747bf1c9a
