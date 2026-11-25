-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_upper_block_rank_one_update
-- name    : PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.upper_block_rank_one_update
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:43.100151+00:00
-- url     : https://prove2.me/theorems/5033ec3d-3f99-4d8a-8fa4-d2f9317b2f5d
-- title:
--   NQ: upper block rank one update
-- statement:
--   The NQ construction uses the upper block rank one update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L81-L96

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
variable {n : ℕ}

theorem PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.upper_block_rank_one_update {i₀ : Fin n} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M.toBlocks₁₁ = 1 + replicateCol Unit (Pi.single i₀ (1 : R)) * replicateRow Unit (fun k => (M - 1) (Sum.inl i₀) (Sum.inl k)) := by sorry
