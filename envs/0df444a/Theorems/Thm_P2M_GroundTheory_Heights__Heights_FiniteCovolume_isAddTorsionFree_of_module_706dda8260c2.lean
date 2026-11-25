-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isAddTorsionFree_of_module_706dda8260c2
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_isAddTorsionFree_of_module_706dda8260c2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:51.156058+00:00
-- url     : https://prove2.me/theorems/27496634-65c3-4cb2-8224-e34908dec94d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume is Add Torsion Free of module 706dda8260c2: P2 M Ground Theory Heights  Heights Finite Covolume is Add Torsion Free of module 706dda8260c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume is Add Torsion Free of module 706dda8260c2 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume is Add Torsion Free of module 706dda8260c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_isAddTorsionFree_of_module_706dda8260c2 (K V : Type*) [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] : IsAddTorsionFree V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«isAddTorsionFree_of_module» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_isAddTorsionFree_of_module_706dda8260c2
