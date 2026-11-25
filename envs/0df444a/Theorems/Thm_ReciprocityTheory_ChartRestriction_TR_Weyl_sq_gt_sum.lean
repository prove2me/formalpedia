-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_gt_sum
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_gt_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:34.008003+00:00
-- url     : https://prove2.me/theorems/689b6168-a990-4d0a-aa74-09607c8072c0
-- title:
--   Weyl: sq gt sum
-- statement:
--   The Weyl construction uses the sq gt sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L254-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L254-L279

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_gt_sum {K : Type*} [Field K] : ∀ (k : ℕ) (κ : Fin k → ℤ), (∀ s, 0 ≤ κ s) →
    ∀ [Fintype (sq_SSZ k κ)] (t : Fin k → K), ∑ g : sq_SSZ k κ, sq_mono t g.1 = gtChar k κ t := by sorry
