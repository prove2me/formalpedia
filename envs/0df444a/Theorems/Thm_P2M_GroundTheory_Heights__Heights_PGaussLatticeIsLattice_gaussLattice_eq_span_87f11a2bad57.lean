-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_gaussLattice_eq_span_87f11a2bad57
-- name    : P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_gaussLattice_eq_span_87f11a2bad57
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:53.057796+00:00
-- url     : https://prove2.me/theorems/1353810d-bfbe-4ba8-a8bc-3dcd0fb0e4da
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice gauss Lattice eq span 87f11a2bad57: P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice gauss Lattice eq span 87f11a2bad57
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice gauss Lattice eq span 87f11a2bad57 construction uses the P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice gauss Lattice eq span 87f11a2bad57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeIsLattice.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeIsLattice.lean#L24-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeIsLattice
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
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussLatticeIsLattice

theorem P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_gaussLattice_eq_span_87f11a2bad57 {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    gaussLattice B = Submodule.span ℤ (Set.range (colBasis B hB)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussLatticeIsLattice».«gaussLattice_eq_span» := P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_gaussLattice_eq_span_87f11a2bad57
