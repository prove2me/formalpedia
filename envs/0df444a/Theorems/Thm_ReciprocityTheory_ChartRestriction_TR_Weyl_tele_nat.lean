-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_tele_nat
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.tele_nat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:23.828137+00:00
-- url     : https://prove2.me/theorems/9dab1610-df68-5d9e-a096-6c1dee3aedfc
-- title:
--   Weyl: tele nat
-- statement:
--   The Weyl construction uses the tele nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L25-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L25-L58

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.tele_nat {K : Type*} [Field K] {t y : K} (ht : t ≠ 0) (hy : y ≠ 0) (c e : ℤ) (k : ℕ) :
    (t - y) * ∑ m ∈ Icc c (c - 1 + k), t ^ (m + e) * y ^ (c - 1 + k - m) =
      t ^ (c - 1 + k + 1 + e) - y ^ (c - 1 + k - c + 1) * t ^ (c + e) := by sorry
