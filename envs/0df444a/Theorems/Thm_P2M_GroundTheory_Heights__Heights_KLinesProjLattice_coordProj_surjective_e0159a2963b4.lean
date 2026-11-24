-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_surjective_e0159a2963b4
-- name    : P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_surjective_e0159a2963b4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:57.52483+00:00
-- url     : https://prove2.me/theorems/1809b61c-ca81-4ce6-b4a0-ebcc95b2f2b9
-- title:
--   P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj surjective e0159a2963b4: P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj surjective e0159a2963b4
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj surjective e0159a2963b4 construction uses the P2 M Ground Theory Heights  Heights KLines Proj Lattice coord Proj surjective e0159a2963b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjLattice.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjLattice.lean#L12-L17

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

theorem P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_surjective_e0159a2963b4 {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesProjLattice».«coordProj_surjective» := P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_surjective_e0159a2963b4
