-- Prove2me | Theorems.Thm_P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c
-- name    : P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:51.145655+00:00
-- url     : https://prove2.me/theorems/bf0eb5e8-5bd9-51e3-88ba-5e83f39da1e3
-- title:
--   P2 M Upper Theory Comparison  host Facts S fb5313d5199c: P2 M Upper Theory Comparison  host Facts S fb5313d5199c
-- statement:
--   The P2 M Upper Theory Comparison  host Facts S fb5313d5199c construction uses the P2 M Upper Theory Comparison  host Facts S fb5313d5199c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/hostFactsS.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/hostFactsS.lean#L127-L136

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_hostFactsS
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

theorem P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c :
    ∀ (φ : Frame) (H : HostAx φ), HostFactsS (arith H.toHostRaw) (insert H.q H.small) := by sorry

alias «UpperTheory».«Comparison₂».«hostFactsS» := P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c
