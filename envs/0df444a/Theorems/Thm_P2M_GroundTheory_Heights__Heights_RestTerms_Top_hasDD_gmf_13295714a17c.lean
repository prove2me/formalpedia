-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:34.243608+00:00
-- url     : https://prove2.me/theorems/9fb1af77-802c-439e-9b44-16be1889fec5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD gmf 13295714a17c: P2 M Ground Theory Heights  Heights Rest Terms Top has DD gmf 13295714a17c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD gmf 13295714a17c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD gmf 13295714a17c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L24-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c (hF : FrobeniusCharacterFormula.Statement) (f r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q : Fin f → ℕ) (e : ℕ) :
    HasDD f (r + a) (gmf f r a c q e) (gmfOut f r a c κ q e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_gmf» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_gmf_13295714a17c
