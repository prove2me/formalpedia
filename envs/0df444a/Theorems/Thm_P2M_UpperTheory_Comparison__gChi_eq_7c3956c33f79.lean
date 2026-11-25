-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__gChi_eq_7c3956c33f79
-- name    : P2M_UpperTheory_Comparison__gChi_eq_7c3956c33f79
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:01.159441+00:00
-- url     : https://prove2.me/theorems/86de3b1c-6ffa-4a5a-93b4-0a8334e54f37
-- title:
--   P2 M Upper Theory Comparison  g Chi eq 7c3956c33f79: P2 M Upper Theory Comparison  g Chi eq 7c3956c33f79
-- statement:
--   The P2 M Upper Theory Comparison  g Chi eq 7c3956c33f79 construction uses the P2 M Upper Theory Comparison  g Chi eq 7c3956c33f79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/GChiEq.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/GChiEq.lean#L16-L36

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GChiEq
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

theorem P2M_UpperTheory_Comparison__gChi_eq_7c3956c33f79 :
    ∀ (ψ : PChar) (y : ℝ), An.gChi ψ.χ y = Deduction.Gchi ψ.χ y := by sorry

alias «UpperTheory».«Comparison₂».«gChi_eq» := P2M_UpperTheory_Comparison__gChi_eq_7c3956c33f79
