-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_HermitianDetMono_one_le_det_one_add_bb3f4c9f8b7a
-- name    : P2M_GroundTheory_Heights__Heights_FourB_HermitianDetMono_one_le_det_one_add_bb3f4c9f8b7a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:34:10.630161+00:00
-- url     : https://prove2.me/theorems/81669d87-465f-42ff-9df6-c6bfb98fcd08
-- title:
--   P2 M Ground Theory Heights  Heights Four B Hermitian Det Mono one le det one add bb3f4c9f8b7a: P2 M Ground Theory Heights  Heights Four B Hermitian Det Mono one le det one add bb3f4c9f8b7a
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Hermitian Det Mono one le det one add bb3f4c9f8b7a construction uses the P2 M Ground Theory Heights  Heights Four B Hermitian Det Mono one le det one add bb3f4c9f8b7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PHermitianDetMono.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PHermitianDetMono.lean#L10-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PHermitianDetMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Matrix
open scoped ComplexOrder MatrixOrder

theorem P2M_GroundTheory_Heights__Heights_FourB_HermitianDetMono_one_le_det_one_add_bb3f4c9f8b7a {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) : 1 ≤ (1 + M).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«HermitianDetMono».«one_le_det_one_add» := P2M_GroundTheory_Heights__Heights_FourB_HermitianDetMono_one_le_det_one_add_bb3f4c9f8b7a
