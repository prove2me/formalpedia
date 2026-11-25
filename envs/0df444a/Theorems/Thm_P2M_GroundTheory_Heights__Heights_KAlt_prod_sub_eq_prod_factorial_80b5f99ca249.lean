-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_prod_sub_eq_prod_factorial_80b5f99ca249
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_prod_sub_eq_prod_factorial_80b5f99ca249
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:56.639406+00:00
-- url     : https://prove2.me/theorems/9416b8d8-7a65-47ed-b5d9-fc6a471b3bd0
-- title:
--   P2 M Ground Theory Heights  Heights KAlt prod sub eq prod factorial 80b5f99ca249: P2 M Ground Theory Heights  Heights KAlt prod sub eq prod factorial 80b5f99ca249
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt prod sub eq prod factorial 80b5f99ca249 construction uses the P2 M Ground Theory Heights  Heights KAlt prod sub eq prod factorial 80b5f99ca249 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L27-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L27-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
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
open Finset
open GroundTheory.Heights₂.Heights.KAlt

theorem P2M_GroundTheory_Heights__Heights_KAlt_prod_sub_eq_prod_factorial_80b5f99ca249 : ∀ r : ℕ,
    (∏ a : Fin r, ∏ b : Fin r, if a < b then ((b : ℕ) : ℚ) - ((a : ℕ) : ℚ) else 1) =
      ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«prod_sub_eq_prod_factorial» := P2M_GroundTheory_Heights__Heights_KAlt_prod_sub_eq_prod_factorial_80b5f99ca249
