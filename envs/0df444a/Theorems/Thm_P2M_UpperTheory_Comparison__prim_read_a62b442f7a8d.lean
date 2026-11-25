-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__prim_read_a62b442f7a8d
-- name    : P2M_UpperTheory_Comparison__prim_read_a62b442f7a8d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:28.412323+00:00
-- url     : https://prove2.me/theorems/9c58a696-f396-4d09-adb3-7f03321e7656
-- title:
--   P2 M Upper Theory Comparison  prim read a62b442f7a8d: P2 M Upper Theory Comparison  prim read a62b442f7a8d
-- statement:
--   The P2 M Upper Theory Comparison  prim read a62b442f7a8d construction uses the P2 M Upper Theory Comparison  prim read a62b442f7a8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean#L48-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean#L48-L97

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimRead
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

theorem P2M_UpperTheory_Comparison__prim_read_a62b442f7a8d :
    ∀ (φ : Frame) (H : HostAx φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), HostAddCharCompatible H.toHostRaw ell → ∀ ψ : AddChar (E0 × φ.A) ℂ,
      (ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (H.toHostRaw.prim (chr φ ψ)).χ) ∧
        ∀ y, GPsi (arith H.toHostRaw) ell ψ y = An.gChi (H.toHostRaw.prim (chr φ ψ)).χ y := by sorry

alias «UpperTheory».«Comparison₂».«prim_read» := P2M_UpperTheory_Comparison__prim_read_a62b442f7a8d
