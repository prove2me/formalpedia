-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_antitone_of_mem_interl
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.antitone_of_mem_interl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:08.288394+00:00
-- url     : https://prove2.me/theorems/d1d461bc-0d53-5a66-9bcc-ee3a3462a9ab
-- title:
--   Weyl: antitone of mem interl
-- statement:
--   The Weyl construction uses the antitone of mem interl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L66-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.antitone_of_mem_interl {n : ℕ} {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) {mu : Fin n → ℤ}
    (hmu : mu ∈ interl lam) : Antitone mu := by sorry
