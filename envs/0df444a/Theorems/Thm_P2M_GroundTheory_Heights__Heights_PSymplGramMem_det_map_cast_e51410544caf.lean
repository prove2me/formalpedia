-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplGramMem_det_map_cast_e51410544caf
-- name    : P2M_GroundTheory_Heights__Heights_PSymplGramMem_det_map_cast_e51410544caf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:05.798804+00:00
-- url     : https://prove2.me/theorems/ee55a4c8-c0e1-5d85-9133-85a57d596273
-- title:
--   P2 M Ground Theory Heights  Heights PSympl Gram Mem det map cast e51410544caf: P2 M Ground Theory Heights  Heights PSympl Gram Mem det map cast e51410544caf
-- statement:
--   The P2 M Ground Theory Heights  Heights PSympl Gram Mem det map cast e51410544caf construction uses the P2 M Ground Theory Heights  Heights PSympl Gram Mem det map cast e51410544caf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplGramMem.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplGramMem.lean#L11-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplGramMem
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
open GroundTheory.Heights₂.Heights.PSymplGramMem

theorem P2M_GroundTheory_Heights__Heights_PSymplGramMem_det_map_cast_e51410544caf {n : ℕ} {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hP : P ∈ symplecticGroup (Fin n) ℤ) : (P.map (Int.cast : ℤ → ℝ)).det = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PSymplGramMem».«det_map_cast» := P2M_GroundTheory_Heights__Heights_PSymplGramMem_det_map_cast_e51410544caf
