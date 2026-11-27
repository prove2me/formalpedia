-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_C4_Bq_NQ_conj
-- name    : PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:45.601894+00:00
-- url     : https://prove2.me/theorems/271808fd-0433-4a73-9099-0e18a5ecbd5c
-- title:
--   NQ: conj
-- statement:
--   The NQ construction uses the conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L18-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ParabolicBlockForms/UpperBlockRankOneUpdate.lean#L18-L46

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

theorem PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.conj {x y : ι} (hxy : x ≠ y) {J J' M : Matrix ι ι R} (hJ : Pad x y J) (hJ' : Pad x y J')
    (hJJ : J * J' = 1) (hM : NQ x y M) : NQ x y (J * M * J') := by sorry
