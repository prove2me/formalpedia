-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_prod_zpow_eq
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.prod_zpow_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:34.788562+00:00
-- url     : https://prove2.me/theorems/2edc156e-f7bb-4b6f-bd0b-96a7df17a4e7
-- title:
--   Weyl: prod zpow eq
-- statement:
--   The Weyl construction uses the prod zpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L18-L23

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.prod_zpow_eq {K : Type*} [Field K] {y : K} (hy : y ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, y ^ f i = y ^ (∑ i ∈ s, f i) := by sorry
