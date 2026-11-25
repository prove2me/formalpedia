-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_blk_strictMono
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.blk_strictMono
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:27:01.053238+00:00
-- url     : https://prove2.me/theorems/5847898c-11f4-4bf0-824a-d1d631af860d
-- title:
--   Weyl: blk strict Mono
-- statement:
--   The Weyl construction uses the blk strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/BlockCombStatement.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/BlockCombStatement.lean#L35-L36

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.blk_strictMono {n : ℕ} (ε : Fin n → Bool) (b : Bool) : StrictMono (blk ε b) := by sorry
