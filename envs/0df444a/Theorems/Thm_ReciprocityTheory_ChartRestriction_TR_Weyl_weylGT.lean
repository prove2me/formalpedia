-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_weylGT
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:32.531885+00:00
-- url     : https://prove2.me/theorems/0955b533-8cd2-4689-a480-b89bfcd98fc1
-- title:
--   Weyl: weyl GT
-- statement:
--   The Weyl construction uses the weyl GT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L178-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AntitoneOfMemInterl.lean#L178-L189

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT : WeylGTStatement := by sorry
