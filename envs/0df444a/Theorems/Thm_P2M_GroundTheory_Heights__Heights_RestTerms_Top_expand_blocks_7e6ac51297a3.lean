-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_expand_blocks_7e6ac51297a3
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_expand_blocks_7e6ac51297a3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:37.898816+00:00
-- url     : https://prove2.me/theorems/32694439-4ece-4b77-b944-25e69ed64e38
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top expand blocks 7e6ac51297a3: P2 M Ground Theory Heights  Heights Rest Terms Top expand blocks 7e6ac51297a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top expand blocks 7e6ac51297a3 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top expand blocks 7e6ac51297a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L301-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L301-L313

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_expand_blocks_7e6ac51297a3 (f r a : ℕ) (c : SmallBlock) (g : Fin f → MvPolynomial (Fin r) ℚ) (e : ℕ) :
    (∏ σ, blockEmb f (r + a) σ (yEval r a c (g σ))) * smallBlockMu f r a c ^ e *
        fibreClass f r a c =
      ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e,
        (Nat.multinomial Finset.univ m : ℚ) •
          ∏ σ, blockEmb f (r + a) σ
            (yEval r a c (g σ * psum (Fin r) ℚ 1 ^ m σ) * fib1 r a c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«expand_blocks» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_expand_blocks_7e6ac51297a3
