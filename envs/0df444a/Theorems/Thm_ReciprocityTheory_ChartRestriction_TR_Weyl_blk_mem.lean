-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_blk_mem
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.blk_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:26:35.253559+00:00
-- url     : https://prove2.me/theorems/8f7d5dbd-42e0-4cd7-bf53-d12b70bcd6f4
-- title:
--   Weyl: blk mem
-- statement:
--   The Weyl construction uses the blk mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/BlockCombStatement.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/BlockCombStatement.lean#L31-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.blk_mem {n : ℕ} (ε : Fin n → Bool) (b : Bool) (r : Fin (cnt ε b)) : ε (blk ε b r) = b := by sorry
