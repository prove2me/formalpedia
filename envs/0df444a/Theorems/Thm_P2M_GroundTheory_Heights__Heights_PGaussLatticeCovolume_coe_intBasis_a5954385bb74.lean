-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_coe_intBasis_a5954385bb74
-- name    : P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_coe_intBasis_a5954385bb74
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:31.160911+00:00
-- url     : https://prove2.me/theorems/c46dddf0-0cd4-44a9-8991-cba28cf7c1b7
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Lattice Covolume coe int Basis a5954385bb74: P2 M Ground Theory Heights  Heights PGauss Lattice Covolume coe int Basis a5954385bb74
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Lattice Covolume coe int Basis a5954385bb74 construction uses the P2 M Ground Theory Heights  Heights PGauss Lattice Covolume coe int Basis a5954385bb74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCovolume.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCovolume.lean#L42-L45

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

theorem P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_coe_intBasis_a5954385bb74 {g : ℕ} {B : Matrix (Fin g) (Fin g) ℝ} (hB : B.det ≠ 0) :
    ((↑) : gaussLattice B → EuclideanSpace ℝ (Fin g)) ∘ intBasis hB = cols B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussLatticeCovolume».«coe_intBasis» := P2M_GroundTheory_Heights__Heights_PGaussLatticeCovolume_coe_intBasis_a5954385bb74
