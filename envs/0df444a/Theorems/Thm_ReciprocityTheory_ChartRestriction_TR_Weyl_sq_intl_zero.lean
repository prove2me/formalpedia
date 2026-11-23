-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_intl_zero
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_intl_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:58.958615+00:00
-- url     : https://prove2.me/theorems/8e8f3149-3401-4171-8ba7-9860c433f95a
-- title:
--   Weyl: sq intl zero
-- statement:
--   The Weyl construction uses the sq intl zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L42-L59

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_intl_zero {k : ℕ} (f : Fin k → Fin k → ℕ) (hf : sq_Intl f) :
    ∀ (tv : ℕ) (t : Fin k), t.val = tv → ∀ a : Fin k, a.val < tv → f a t = 0 := by sorry
