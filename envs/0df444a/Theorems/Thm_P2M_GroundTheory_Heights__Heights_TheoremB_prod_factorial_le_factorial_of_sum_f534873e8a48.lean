-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_prod_factorial_le_factorial_of_sum_f534873e8a48
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_prod_factorial_le_factorial_of_sum_f534873e8a48
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:11.684474+00:00
-- url     : https://prove2.me/theorems/e74b36b7-5bc6-51d2-8299-70ea1b406ce0
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B prod factorial le factorial of sum f534873e8a48: P2 M Ground Theory Heights  Heights Theorem B prod factorial le factorial of sum f534873e8a48
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B prod factorial le factorial of sum f534873e8a48 construction uses the P2 M Ground Theory Heights  Heights Theorem B prod factorial le factorial of sum f534873e8a48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationBound.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/PPolarisationBound.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_PPolarisationBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_TheoremB_prod_factorial_le_factorial_of_sum_f534873e8a48 {σ : Type*} (m : σ →₀ ℕ) (n : ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    (m.prod fun _ e => (e.factorial : ℝ)) ≤ (n.factorial : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«prod_factorial_le_factorial_of_sum» := P2M_GroundTheory_Heights__Heights_TheoremB_prod_factorial_le_factorial_of_sum_f534873e8a48
