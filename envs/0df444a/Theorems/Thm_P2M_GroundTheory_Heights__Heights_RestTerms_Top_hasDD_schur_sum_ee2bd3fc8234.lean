-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_sum_ee2bd3fc8234
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_sum_ee2bd3fc8234
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:30.198196+00:00
-- url     : https://prove2.me/theorems/61d0a227-a721-54d8-9e32-579e9588ad27
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur sum ee2bd3fc8234: P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur sum ee2bd3fc8234
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur sum ee2bd3fc8234 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD schur sum ee2bd3fc8234 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L266-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L266-L276

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_sum_ee2bd3fc8234 (r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (s : Finset (Fin r → ℕ)) (hs : ∀ lam ∈ s, Antitone lam) (b : (Fin r → ℕ) → ℚ) :
    HasDD 1 (r + a) (yEval r a c (∑ lam ∈ s, C (b lam) * schur (Fin r) lam) * fib1 r a c)
      (∑ lam ∈ s, b lam • pushOut r a c κ lam) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_schur_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_schur_sum_ee2bd3fc8234
