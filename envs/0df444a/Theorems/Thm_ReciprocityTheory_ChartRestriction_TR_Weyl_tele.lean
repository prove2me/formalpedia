-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_tele
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.tele
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:45.077806+00:00
-- url     : https://prove2.me/theorems/aa3168c9-d34a-4c5f-b1c9-0512605ee548
-- title:
--   Weyl: tele
-- statement:
--   The Weyl construction uses the tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L60-L64

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.tele {K : Type*} [Field K] {t y : K} (ht : t ≠ 0) (hy : y ≠ 0) (c b e : ℤ) (h : c ≤ b + 1) :
    (t - y) * ∑ m ∈ Icc c b, t ^ (m + e) * y ^ (b - m) = t ^ (b + 1 + e) - y ^ (b - c + 1) * t ^ (c + e) := by sorry
