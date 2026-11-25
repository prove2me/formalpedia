-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_TR_Weyl_sq_mono_split
-- name    : ReciprocityTheory.ChartRestriction.TR.Weyl.sq_mono_split
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:29.867632+00:00
-- url     : https://prove2.me/theorems/a9140da1-d882-4e90-8011-d09f61efa176
-- title:
--   Weyl: sq mono split
-- statement:
--   The Weyl construction uses the sq mono split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L226-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean#L226-L252

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

theorem ReciprocityTheory.ChartRestriction.TR.Weyl.sq_mono_split {K : Type*} [Field K] {k : ℕ} (μ : Fin (k + 1) → ℤ) (t : Fin (k + 1) → K)
    (g : sq_SSZ (k + 1) μ) :
    sq_mono t g.1 = sq_mono (fun i => t i.castSucc) (sq_restr g.1) *
      t (Fin.last k) ^ (wsum μ - wsum (fun s => ((∑ a, sq_restr g.1 a s : ℕ) : ℤ))) := by sorry
