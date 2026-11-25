-- Prove2me | Theorems.Thm_P2M_Formalism_NuclearRankWeightBounds_P_rank_add_le__c793ac3f6c26
-- name    : P2M_Formalism_NuclearRankWeightBounds_P_rank_add_le__c793ac3f6c26
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:10.074827+00:00
-- url     : https://prove2.me/theorems/24117708-b851-4b64-85d7-e624ee391b26
-- title:
--   P2 M Formalism Nuclear Rank Weight Bounds P rank add le  c793ac3f6c26: P2 M Formalism Nuclear Rank Weight Bounds P rank add le  c793ac3f6c26
-- statement:
--   The P2 M Formalism Nuclear Rank Weight Bounds P rank add le  c793ac3f6c26 construction uses the P2 M Formalism Nuclear Rank Weight Bounds P rank add le  c793ac3f6c26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/RankLeOfSupport.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/RankLeOfSupport.lean#L7-L16

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_RankLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Finset

theorem P2M_Formalism_NuclearRankWeightBounds_P_rank_add_le__c793ac3f6c26 {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by sorry

alias «Formalism».«NuclearRankWeightBounds».«P».«rank_add_le'» := P2M_Formalism_NuclearRankWeightBounds_P_rank_add_le__c793ac3f6c26
