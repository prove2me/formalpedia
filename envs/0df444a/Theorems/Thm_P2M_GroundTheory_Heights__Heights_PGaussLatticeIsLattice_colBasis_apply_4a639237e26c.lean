-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_colBasis_apply_4a639237e26c
-- name    : P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_colBasis_apply_4a639237e26c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:32.939145+00:00
-- url     : https://prove2.me/theorems/093579c8-e1e2-49ce-ac0b-8cb8ba6fe8b0
-- title:
--   P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice col Basis apply 4a639237e26c: P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice col Basis apply 4a639237e26c
-- statement:
--   The P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice col Basis apply 4a639237e26c construction uses the P2 M Ground Theory Heights  Heights PGauss Lattice Is Lattice col Basis apply 4a639237e26c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeIsLattice.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeIsLattice.lean#L19-L22

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

theorem P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_colBasis_apply_4a639237e26c {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) (i : Fin g) :
    colBasis B hB i = WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PGaussLatticeIsLattice».«colBasis_apply» := P2M_GroundTheory_Heights__Heights_PGaussLatticeIsLattice_colBasis_apply_4a639237e26c
