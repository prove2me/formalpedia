-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__card_PsiA_f174cd9d4385
-- name    : P2M_UpperTheory_Comparison__card_PsiA_f174cd9d4385
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:03:22.133845+00:00
-- url     : https://prove2.me/theorems/ab53d928-c142-59a2-8eb3-0e3a1d3b0918
-- title:
--   P2 M Upper Theory Comparison  card Psi A f174cd9d4385: P2 M Upper Theory Comparison  card Psi A f174cd9d4385
-- statement:
--   The P2 M Upper Theory Comparison  card Psi A f174cd9d4385 construction uses the P2 M Upper Theory Comparison  card Psi A f174cd9d4385 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/CardPsiA.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/CardPsiA.lean#L60-L63

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CardPsiA
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

theorem P2M_UpperTheory_Comparison__card_PsiA_f174cd9d4385 :
    ∀ φ : Frame, (PsiA φ.A0).card = 4 * φ.o := by sorry

alias «UpperTheory».«Comparison₂».«card_PsiA» := P2M_UpperTheory_Comparison__card_PsiA_f174cd9d4385
