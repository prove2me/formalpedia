-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealStdIndex_idealLattice_toAddSubgroup_d2db4e91f501
-- name    : P2M_GroundTheory_Heights__Heights_KLinesIdealStdIndex_idealLattice_toAddSubgroup_d2db4e91f501
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:54.915731+00:00
-- url     : https://prove2.me/theorems/45e0caf3-9977-439e-8f2d-fc4941088cd4
-- title:
--   P2 M Ground Theory Heights  Heights KLines Ideal Std Index ideal Lattice to Add Subgroup d2db4e91f501: P2 M Ground Theory Heights  Heights KLines Ideal Std Index ideal Lattice to Add Subgroup d2db4e91
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Ideal Std Index ideal Lattice to Add Subgroup d2db4e91f501 construction uses the P2 M Ground Theory Heights  Heights KLines Ideal Std Index ideal Lattice to Add Subgroup d2db4e91f501 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealStdIndex.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealStdIndex.lean#L12-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealStdIndex
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
open GroundTheory.Heights₂.Heights.KLinesIdealStdIndex

theorem P2M_GroundTheory_Heights__Heights_KLinesIdealStdIndex_idealLattice_toAddSubgroup_d2db4e91f501 {K : Type} [Field K] {k : ℕ}
    (a : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).toAddSubgroup =
      AddSubgroup.pi Set.univ fun j => (a j : Submodule (𝓞 K) K).toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesIdealStdIndex».«idealLattice_toAddSubgroup» := P2M_GroundTheory_Heights__Heights_KLinesIdealStdIndex_idealLattice_toAddSubgroup_d2db4e91f501
