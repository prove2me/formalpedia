-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_SSZ_finite
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_SSZ_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:11.092522+00:00
-- url     : https://prove2.me/theorems/6235a482-7c33-45b4-a231-9ba17579b371
-- title:
--   Weyl: sq SSZ finite
-- statement:
--   The Weyl construction uses the sq SSZ finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L198-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L198-L212

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_SSZ_finite (k : ℕ) (κ : Fin k → ℤ) : Finite (sq_SSZ k κ) := by sorry
