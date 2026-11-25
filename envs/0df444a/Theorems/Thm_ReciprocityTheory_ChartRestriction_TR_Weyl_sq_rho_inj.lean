-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_rho_inj
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_rho_inj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:36.196409+00:00
-- url     : https://prove2.me/theorems/e354edea-2655-416d-8b87-170629f9a921
-- title:
--   Weyl: sq rho inj
-- statement:
--   The Weyl construction uses the sq rho inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L95-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L95-L127

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_rho_inj {k : ℕ} (μ : Fin (k + 1) → ℤ) : Function.Injective (sq_rho μ) := by sorry
