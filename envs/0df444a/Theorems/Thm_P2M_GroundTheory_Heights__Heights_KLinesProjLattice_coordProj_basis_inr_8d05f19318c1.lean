-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_basis_inr_8d05f19318c1
-- name    : P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_basis_inr_8d05f19318c1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:20.04348+00:00
-- url     : https://prove2.me/theorems/2abb4d6f-b97e-46bf-87ef-0e8ab4a5274e
-- title:
--   P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj basis inr 8d05f19318c1: P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj basis inr 8d05f19318c1
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj basis inr 8d05f19318c1 construction uses the P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj basis inr 8d05f19318c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjLattice.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjLattice.lean#L19-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProjLattice
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
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesProjLattice

theorem P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_basis_inr_8d05f19318c1 {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (j : Fin k) :
    coordProj B (B (Sum.inr j)) = Pi.single j 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesProjLattice».«coordProj_basis_inr» := P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_basis_inr_8d05f19318c1
