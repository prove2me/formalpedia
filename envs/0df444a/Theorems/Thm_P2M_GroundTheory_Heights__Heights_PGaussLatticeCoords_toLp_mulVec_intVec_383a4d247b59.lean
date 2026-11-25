-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeCoords_toLp_mulVec_intVec_383a4d247b59
-- name    : P2M_GroundTheory_Heights__Heights_PGaussLatticeCoords_toLp_mulVec_intVec_383a4d247b59
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:08.490832+00:00
-- url     : https://prove2.me/theorems/3e3e79f8-fbb5-4ab1-8f2c-ae4e02faf558
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Lattice Coords to Lp mul Vec int Vec 383a4d247b59: P2 M Ground Theory Heights  Heights PGauss Lattice Coords to Lp mul Vec int Vec 383a4d247b59
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Lattice Coords to Lp mul Vec int Vec 383a4d247b59 construction uses the P2 M Ground Theory Heights  Heights PGauss Lattice Coords to Lp mul Vec int Vec 383a4d247b59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCoords.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeCoords.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeCoords
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
open Matrix
open GroundTheory.Heights₂.Heights.PGaussLatticeCoords

theorem P2M_GroundTheory_Heights__Heights_PGaussLatticeCoords_toLp_mulVec_intVec_383a4d247b59 {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (k : Fin g → ℤ) :
    WithLp.toLp 2 (B *ᵥ intVec k) = ∑ i, k i • WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussLatticeCoords».«toLp_mulVec_intVec» := P2M_GroundTheory_Heights__Heights_PGaussLatticeCoords_toLp_mulVec_intVec_383a4d247b59
