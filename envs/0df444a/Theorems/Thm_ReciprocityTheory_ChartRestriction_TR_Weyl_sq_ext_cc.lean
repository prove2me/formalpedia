-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_cc
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:47.197539+00:00
-- url     : https://prove2.me/theorems/0c3f9d63-5175-4534-a560-96689f36ec11
-- title:
--   Weyl: sq ext cc
-- statement:
--   The Weyl construction uses the sq ext cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L135-L136

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_cc {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (a t : Fin k) :
    sq_ext μ g a.castSucc t.castSucc = g a t := by sorry
