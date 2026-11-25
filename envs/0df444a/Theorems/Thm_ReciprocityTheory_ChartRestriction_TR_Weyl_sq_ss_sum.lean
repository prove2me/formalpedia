-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ss_sum
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ss_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:13.836238+00:00
-- url     : https://prove2.me/theorems/54f1b16e-424a-53a0-b56d-3f4bfaa446a7
-- title:
--   Weyl: sq ss sum
-- statement:
--   The Weyl construction uses the sq ss sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqChar.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqChar.lean#L64-L69

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ss_sum {K : Type*} [Field K] (N : ℕ) (ν : Fin N → ℕ) [Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν)]
    (t : Fin N → K) :
    ∑ m : ↥(Formalism.GradedWeylDivisibility.ssIdx N N ν), ∏ a, t a ^ Formalism.GradedWeylDivisibility.rowWt m.1 a = gtChar N (fun i => (ν i : ℤ)) t := by sorry
