-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__chr_bij_14af8101f3b5
-- name    : P2M_UpperTheory_Comparison__chr_bij_14af8101f3b5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:04.828718+00:00
-- url     : https://prove2.me/theorems/deaaa6cb-42e2-5818-b0ce-8852fae59abb
-- title:
--   P2 M Upper Theory Comparison  chr bij 14af8101f3b5: P2 M Upper Theory Comparison  chr bij 14af8101f3b5
-- statement:
--   The P2 M Upper Theory Comparison  chr bij 14af8101f3b5 construction uses the P2 M Upper Theory Comparison  chr bij 14af8101f3b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/ChrBij.lean#L21-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/ChrBij.lean#L21-L90

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ChrBij
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

theorem P2M_UpperTheory_Comparison__chr_bij_14af8101f3b5 :
    ∀ φ : Frame, Function.Bijective (chr φ) ∧ chr φ 0 = 1 ∧ chr φ chC = φ.chC ∧ chr φ psC = φ.psC ∧
      (∀ ψ g, ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g))) ∧
      (∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ)) ∧ ∀ ψ, chr φ ψ ∈ φ.Xp ↔ (ψ ∈ PsiA φ.A0 ∧ ψ sgc0 = 1) := by sorry

alias «UpperTheory».«Comparison₂».«chr_bij» := P2M_UpperTheory_Comparison__chr_bij_14af8101f3b5
