-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_ext_cl
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:09.380075+00:00
-- url     : https://prove2.me/theorems/2ab75d1a-0956-4764-b527-b396e990f0c8
-- title:
--   Weyl: sq ext cl
-- statement:
--   The Weyl construction uses the sq ext cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L138-L139

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_ext_cl {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (a : Fin k) :
    sq_ext μ g a.castSucc (Fin.last k) = 0 := by sorry
