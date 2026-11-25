-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_dotForm_apply_14b583c97b83
-- name    : P2M_GroundTheory_Heights__Heights_dotForm_apply_14b583c97b83
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:10.481171+00:00
-- url     : https://prove2.me/theorems/0ae31ec9-6e1b-40f2-bc17-90a5f2a2f928
-- title:
--   P2 M Ground Theory Heights  Heights dot Form apply 14b583c97b83: P2 M Ground Theory Heights  Heights dot Form apply 14b583c97b83
-- statement:
--   The P2 M Ground Theory Heights  Heights dot Form apply 14b583c97b83 construction uses the P2 M Ground Theory Heights  Heights dot Form apply 14b583c97b83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean#L28-L28

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

theorem P2M_GroundTheory_Heights__Heights_dotForm_apply_14b583c97b83 (w v : Fin n → ℂ) : dotForm w v = ∑ j, w j * v j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«dotForm_apply» := P2M_GroundTheory_Heights__Heights_dotForm_apply_14b583c97b83
