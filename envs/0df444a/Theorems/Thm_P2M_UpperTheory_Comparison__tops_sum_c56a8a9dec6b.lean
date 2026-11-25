-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__tops_sum_c56a8a9dec6b
-- name    : P2M_UpperTheory_Comparison__tops_sum_c56a8a9dec6b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:29.637911+00:00
-- url     : https://prove2.me/theorems/1b86b56b-a23b-45bb-bc1d-eb52475f2277
-- title:
--   P2 M Upper Theory Comparison  tops sum c56a8a9dec6b: P2 M Upper Theory Comparison  tops sum c56a8a9dec6b
-- statement:
--   The P2 M Upper Theory Comparison  tops sum c56a8a9dec6b construction uses the P2 M Upper Theory Comparison  tops sum c56a8a9dec6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/TopsSum.lean#L75-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/TopsSum.lean#L75-L103

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_TopsSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem P2M_UpperTheory_Comparison__tops_sum_c56a8a9dec6b :
    ∀ (φ : Frame) (TT : Finset φ.A) (δ : ℝ), φ.Shares TT δ → ∀ ψ ∈ PsiA φ.A0, (¬ ∀ h : φ.A, ψ (0, h) = 1) →
      ‖(∑ t ∈ TT, ψ (0, t)) - (((3 * (φ.o : ℝ) + 1)⁻¹ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤ φ.o * δ * (TT.card : ℝ) := by sorry

alias «UpperTheory».«Comparison₂».«tops_sum» := P2M_UpperTheory_Comparison__tops_sum_c56a8a9dec6b
