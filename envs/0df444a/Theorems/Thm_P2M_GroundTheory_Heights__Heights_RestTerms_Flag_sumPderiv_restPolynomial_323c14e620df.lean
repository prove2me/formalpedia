-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_restPolynomial_323c14e620df
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_restPolynomial_323c14e620df
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:59.398488+00:00
-- url     : https://prove2.me/theorems/26702d60-e9e6-58cf-9fe3-8d9197dbfafd
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv rest Polynomial 323c14e620df: P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv rest Polynomial 323c14e620df
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv rest Polynomial 323c14e620df construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag sum Pderiv rest Polynomial 323c14e620df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L302-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L302-L315

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_restPolynomial_323c14e620df (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (s : Finset (Fin (r + a)))
    (α β : Fin f → ℚ)
    (hy : ∀ σ i, (if (yIndex f r a c σ i).1 = τ ∧ (yIndex f r a c σ i).2 ∈ s then 1 else 0 : ℕ) =
      (α σ : ℚ))
    (hz : ∀ σ i, (if (zIndex f r a c σ i).1 = τ ∧ (zIndex f r a c σ i).2 ∈ s then 1 else 0 : ℕ) =
      (β σ : ℚ)) :
    ∑ i ∈ s, pderiv (τ, i) (restPolynomial f r a c) =
      C (((f * (r * a) + 1 : ℕ) : ℚ) * (c.sign * r * ∑ σ, α σ)) *
        (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«sumPderiv_restPolynomial» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_restPolynomial_323c14e620df
