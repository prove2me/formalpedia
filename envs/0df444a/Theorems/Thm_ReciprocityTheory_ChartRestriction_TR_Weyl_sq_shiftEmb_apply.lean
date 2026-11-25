-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_shiftEmb_apply
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_shiftEmb_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:00:44.59291+00:00
-- url     : https://prove2.me/theorems/f7a3cda7-3e5c-5fd1-9ce5-25713a10a475
-- title:
--   Weyl: sq shift Emb apply
-- statement:
--   The Weyl construction uses the sq shift Emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqChar.lean#L37-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqChar.lean#L37-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqChar
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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_shiftEmb_apply {n : ℕ} (c : ℤ) (mu : Fin n → ℤ) : sq_shiftEmb c mu = fun i => mu i + c := by sorry
