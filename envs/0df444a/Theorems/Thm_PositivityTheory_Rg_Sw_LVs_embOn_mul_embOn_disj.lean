-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_embOn_mul_embOn_disj
-- name    : PositivityTheory.Rg.Sw.LVs.embOn_mul_embOn_disj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:19.237642+00:00
-- url     : https://prove2.me/theorems/7d7bfbaf-061e-5948-b89a-e6e827ce439d
-- title:
--   LVs: emb On mul emb On disj
-- statement:
--   The LVs construction uses the emb On mul emb On disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L152-L161

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PositivityTheory.Rg.Sw.LVs.embOn_mul_embOn_disj {s t : Finset (Fin n)} (hst : ∀ c, c ∈ s → c ∉ t) (T : Matrix s s ℂ) (S : Matrix t t ℂ) :
    embOn s T * embOn t S = 0 := by sorry
