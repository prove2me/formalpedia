-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__charsA_aeb36eedc800
-- name    : P2M_UpperTheory_Comparison__charsA_aeb36eedc800
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:21.114291+00:00
-- url     : https://prove2.me/theorems/31a49d4f-73aa-546c-b9f9-c78618070536
-- title:
--   P2 M Upper Theory Comparison  chars A aeb36eedc800: P2 M Upper Theory Comparison  chars A aeb36eedc800
-- statement:
--   The P2 M Upper Theory Comparison  chars A aeb36eedc800 construction uses the P2 M Upper Theory Comparison  chars A aeb36eedc800 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/charsA.lean#L80-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/charsA.lean#L80-L125

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimRead
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CardPsiA
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_TopsSum
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_charsA
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

theorem P2M_UpperTheory_Comparison__charsA_aeb36eedc800 :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), 0 < x →
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell →
        CharsA ell φ.A0 (keptA Λ H.toHostRaw) TT (3 * (Λ.o : ℝ) + 1)⁻¹ (4 * (Λ.o : ℝ)) (koOf Λ) C eps x := by sorry

alias «UpperTheory».«Comparison₂».«charsA» := P2M_UpperTheory_Comparison__charsA_aeb36eedc800
