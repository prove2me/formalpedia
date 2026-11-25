-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_block_981b1a2de18d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_block_981b1a2de18d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:22:34.303837+00:00
-- url     : https://prove2.me/theorems/30ddbe53-2ee1-43d4-81ba-81121e09ec65
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD block 981b1a2de18d: P2 M Ground Theory Heights  Heights Rest Terms Top has DD block 981b1a2de18d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD block 981b1a2de18d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD block 981b1a2de18d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L354-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L354-L361

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_block_981b1a2de18d (hF : FrobeniusCharacterFormula.Statement) (r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q m : ℕ) :
    HasDD 1 (r + a) (yEval r a c (extraFactor r q * psum (Fin r) ℚ 1 ^ m) * fib1 r a c)
      (blockOut r a c κ q m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_block» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_block_981b1a2de18d
