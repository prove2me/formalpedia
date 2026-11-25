-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_embOn_mul_embOn_compl
-- name    : PositivityTheory.Rg.Sw.LVs.embOn_mul_embOn_compl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:43.21431+00:00
-- url     : https://prove2.me/theorems/bd7ff7b3-a0b1-4eed-a458-73c6ef7b1261
-- title:
--   LVs: emb On mul emb On compl
-- statement:
--   The LVs construction uses the emb On mul emb On compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L119-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L119-L140

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.embOn_mul_embOn_compl (j : ℕ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) :
    embOn (blkB j) S * embOn (blkA j) T = 0 ∧ embOn (blkA j) T * embOn (blkB j) S = 0 := by sorry
