-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_prod_factorial_le_ed8781dc790b
-- name    : P2M_GroundTheory_Heights__Heights_KAlt_prod_factorial_le_ed8781dc790b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:52.253706+00:00
-- url     : https://prove2.me/theorems/bbf71d28-46c8-4952-bb8e-5281f73ef733
-- title:
--   P2 M Ground Theory Heights  Heights KAlt prod factorial le ed8781dc790b: P2 M Ground Theory Heights  Heights KAlt prod factorial le ed8781dc790b
-- statement:
--   The P2 M Ground Theory Heights  Heights KAlt prod factorial le ed8781dc790b construction uses the P2 M Ground Theory Heights  Heights KAlt prod factorial le ed8781dc790b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L100-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean#L100-L113

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

theorem P2M_GroundTheory_Heights__Heights_KAlt_prod_factorial_le_ed8781dc790b {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    (∏ a : Fin r, ((s + (r - 1 - (a : ℕ))).factorial : ℚ)) *
        ∏ a : Fin r, ((ν a + (r - 1 - (a : ℕ))).factorial : ℚ) ≤
      (∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)) *
        ∏ a : Fin r, ((s + ν a + (r - 1 - (a : ℕ))).factorial : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KAlt».«prod_factorial_le» := P2M_GroundTheory_Heights__Heights_KAlt_prod_factorial_le_ed8781dc790b
