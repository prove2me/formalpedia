-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_sub_C_mem_ker_2ebe1b0d4571
-- name    : P2M_GroundTheory_Heights__Heights_X_sub_C_mem_ker_2ebe1b0d4571
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:10.292151+00:00
-- url     : https://prove2.me/theorems/f26601f2-8a6d-4eda-95f1-cfd7dce260a9
-- title:
--   P2 M Ground Theory Heights  Heights X sub C mem ker 2ebe1b0d4571: P2 M Ground Theory Heights  Heights X sub C mem ker 2ebe1b0d4571
-- statement:
--   The P2 M Ground Theory Heights  Heights X sub C mem ker 2ebe1b0d4571 construction uses the P2 M Ground Theory Heights  Heights X sub C mem ker 2ebe1b0d4571 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L72-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_X_sub_C_mem_ker_2ebe1b0d4571 (p : Fin n → ℂ) (j : Fin n) :
    X j - C (p j) ∈ RingHom.ker (eval p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«X_sub_C_mem_ker» := P2M_GroundTheory_Heights__Heights_X_sub_C_mem_ker_2ebe1b0d4571
