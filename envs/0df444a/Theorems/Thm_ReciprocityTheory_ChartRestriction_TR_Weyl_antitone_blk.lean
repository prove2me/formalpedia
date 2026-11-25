-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_antitone_blk
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.antitone_blk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:25.541799+00:00
-- url     : https://prove2.me/theorems/34af1204-7d3b-50f5-a04e-dd6f5932469a
-- title:
--   Weyl: antitone blk
-- statement:
--   The Weyl construction uses the antitone blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/Statement.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/Statement.lean#L53-L65

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.antitone_blk {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℤ}
    (hdom : ∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) (b : Bool) : Antitone (Λ ∘ blk ε b) := by sorry
