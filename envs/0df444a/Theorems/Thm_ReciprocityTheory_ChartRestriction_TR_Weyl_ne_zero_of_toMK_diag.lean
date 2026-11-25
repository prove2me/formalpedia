-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_ne_zero_of_toMK_diag
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.ne_zero_of_toMK_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:59.971491+00:00
-- url     : https://prove2.me/theorems/4b302e35-59f5-4f85-83a7-1aa66aeac357
-- title:
--   Weyl: ne zero of to MK diag
-- statement:
--   The Weyl construction uses the ne zero of to MK diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/Statement.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/Statement.lean#L40-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
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
open ReciprocityTheory.ChartRestriction.DS.S7

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.ne_zero_of_toMK_diag {n : ℕ} {ε : Fin n → Bool} (k : KG ε) {t : Fin n → ℂ}
    (hk : toMK k = Matrix.diagonal t) (i : Fin n) : t i ≠ 0 := by sorry
