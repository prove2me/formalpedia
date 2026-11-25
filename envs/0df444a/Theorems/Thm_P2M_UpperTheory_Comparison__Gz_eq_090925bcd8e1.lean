-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__Gz_eq_090925bcd8e1
-- name    : P2M_UpperTheory_Comparison__Gz_eq_090925bcd8e1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:17:10.320893+00:00
-- url     : https://prove2.me/theorems/49d9fe40-5a68-5253-b009-8682ded2baf0
-- title:
--   P2 M Upper Theory Comparison  Gz eq 090925bcd8e1: P2 M Upper Theory Comparison  Gz eq 090925bcd8e1
-- statement:
--   The P2 M Upper Theory Comparison  Gz eq 090925bcd8e1 construction uses the P2 M Upper Theory Comparison  Gz eq 090925bcd8e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/GzEq.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/GzEq.lean#L6-L50

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GzEq
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

theorem P2M_UpperTheory_Comparison__Gz_eq_090925bcd8e1 :
    ∀ y : ℝ, Formalism.Gz y = An.G y ∧ An.G y = Deduction.G y := by sorry

alias «UpperTheory».«Comparison₂».«Gz_eq» := P2M_UpperTheory_Comparison__Gz_eq_090925bcd8e1
