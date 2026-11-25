-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_of_blocks
-- name    : PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.of_blocks
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:27.860351+00:00
-- url     : https://prove2.me/theorems/5deb9daf-0bb3-5387-bb87-9867e2118c7e
-- title:
--   NQ: of blocks
-- statement:
--   The NQ construction uses the of blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L105-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L105-L124

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

theorem PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.of_blocks {i₀ : Fin n} {A B D : Matrix (Fin n) (Fin n) R}
    (hA0 : ∀ a, (A - 1) a i₀ = 0) (hA : ∀ a k, a ≠ i₀ → (A - 1) a k = 0)
    (hB : ∀ a k, a ≠ i₀ → k ≠ i₀ → B a k = 0) (hD : ∀ a k, k ≠ i₀ → (D - 1) a k = 0) :
    NQ (Sum.inl i₀) (Sum.inr i₀) (Matrix.fromBlocks A B 0 D) := by sorry
