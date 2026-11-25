-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_wsum_add
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_wsum_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:51:34.65459+00:00
-- url     : https://prove2.me/theorems/82e97c2a-e61c-5d0e-a34e-592becef930c
-- title:
--   Weyl: sq wsum add
-- statement:
--   The Weyl construction uses the sq wsum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqChar.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqChar.lean#L30-L32

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_wsum_add {n : ℕ} (lam : Fin n → ℤ) (c : ℤ) :
    wsum (fun i => lam i + c) = wsum lam + n * c := by sorry
