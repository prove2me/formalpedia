-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_intl
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_intl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:12.045457+00:00
-- url     : https://prove2.me/theorems/5933d6dc-fcca-5c32-8148-1bf2e4dcda44
-- title:
--   Weyl: sq ext intl
-- statement:
--   The Weyl construction uses the sq ext intl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L162-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L162-L188

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_intl {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) (g : sq_UU k μ) :
    sq_Intl (sq_ext μ g.1) := by sorry
