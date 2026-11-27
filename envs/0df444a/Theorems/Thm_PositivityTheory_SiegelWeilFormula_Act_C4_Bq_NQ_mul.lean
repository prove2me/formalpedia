-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_mul
-- name    : PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:23.407521+00:00
-- url     : https://prove2.me/theorems/6a0f9397-89f5-5136-8aef-71c99eed4d27
-- title:
--   NQ: mul
-- statement:
--   The NQ construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L48-L60

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

theorem PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.mul {x y : ι} {M N : Matrix ι ι R} (hM : NQ x y M) (hN : NQ x y N) : NQ x y (M * N) := by sorry
