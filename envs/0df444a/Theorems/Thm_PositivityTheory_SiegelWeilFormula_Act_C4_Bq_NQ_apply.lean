-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_apply
-- name    : PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:15.121393+00:00
-- url     : https://prove2.me/theorems/e284eb81-68dd-48ba-8a4a-7684168e9864
-- title:
--   NQ: apply
-- statement:
--   The NQ construction uses the apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L62-L68

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

theorem PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.apply {x y : ι} {M : Matrix ι ι R} (hM : NQ x y M) {k l : ι} (h : l = x ∨ (l ≠ y ∧ k ≠ x)) :
    M k l = (1 : Matrix ι ι R) k l := by sorry
