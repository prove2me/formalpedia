-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__prim_inj_152d5f227536
-- name    : P2M_UpperTheory_Comparison__prim_inj_152d5f227536
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:19.484909+00:00
-- url     : https://prove2.me/theorems/6c352b20-12c8-48ea-858c-308beee506c2
-- title:
--   P2 M Upper Theory Comparison  prim inj 152d5f227536: P2 M Upper Theory Comparison  prim inj 152d5f227536
-- statement:
--   The P2 M Upper Theory Comparison  prim inj 152d5f227536 construction uses the P2 M Upper Theory Comparison  prim inj 152d5f227536 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/PrimInj.lean#L6-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/PrimInj.lean#L6-L27

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimInj
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

theorem P2M_UpperTheory_Comparison__prim_inj_152d5f227536 :
    ∀ (φ : Frame) (H : HostAx φ), Function.Injective H.toHostRaw.prim ∧ H.toHostRaw.prim 1 = PChar.one := by sorry

alias «UpperTheory».«Comparison₂».«prim_inj» := P2M_UpperTheory_Comparison__prim_inj_152d5f227536
