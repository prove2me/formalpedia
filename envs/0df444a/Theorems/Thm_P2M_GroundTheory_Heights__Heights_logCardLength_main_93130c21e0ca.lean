-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_main_93130c21e0ca
-- name    : P2M_GroundTheory_Heights__Heights_logCardLength_main_93130c21e0ca
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:22.719346+00:00
-- url     : https://prove2.me/theorems/1b98f2fc-f1e5-4a4a-baec-e9e2951c6978
-- title:
--   P2 M Ground Theory Heights  Heights log Card Length main 93130c21e0ca: P2 M Ground Theory Heights  Heights log Card Length main 93130c21e0ca
-- statement:
--   The P2 M Ground Theory Heights  Heights log Card Length main 93130c21e0ca construction uses the P2 M Ground Theory Heights  Heights log Card Length main 93130c21e0ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L108-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L108-L174

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
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
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}

theorem P2M_GroundTheory_Heights__Heights_logCardLength_main_93130c21e0ca (n : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module R N] [Finite N], Nat.card N = n →
    FinLoc R N ∧ (Function.support (term R N)).Finite ∧
      Real.log (Nat.card N) = ∑ᶠ m, term R N m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logCardLength».«main» := P2M_GroundTheory_Heights__Heights_logCardLength_main_93130c21e0ca
