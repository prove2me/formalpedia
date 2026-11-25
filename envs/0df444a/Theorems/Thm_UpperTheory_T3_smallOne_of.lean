-- Prove2me | Theorems.Thm_UpperTheory_T3_smallOne_of
-- name    : UpperTheory.T3.smallOne_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:17.936361+00:00
-- url     : https://prove2.me/theorems/5b899a9f-6aea-49c6-b064-aa68f9513fe2
-- title:
--   T3: small One of
-- statement:
--   The T3 construction uses the small One of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/SmallOneOf.lean#L8-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/SmallOneOf.lean#L8-L98

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimesAPIntervalOfPrimesRel
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_SmallOneOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3

theorem UpperTheory.T3.smallOne_of :
    GlobalTheory.Lin.PrimesRel → SmallOne := by sorry
