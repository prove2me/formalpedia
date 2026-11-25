-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_add_of_lt__04023416b8fe
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_add_of_lt__04023416b8fe
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:20.653795+00:00
-- url     : https://prove2.me/theorems/6db4f270-bf50-4dd8-960e-f1315a999d29
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order add of lt  04023416b8fe: P2 M Global Theory Hilbert Samuel PS lex Order add of lt  04023416b8fe
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order add of lt  04023416b8fe construction uses the P2 M Global Theory Hilbert Samuel PS lex Order add of lt  04023416b8fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L24-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
variable {D : ℕ}

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_add_of_lt__04023416b8fe {g h : MvPowerSeries (Fin D) ℂ} (hlt : lexOrder g < lexOrder h) :
    lexOrder (g + h) = lexOrder g := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_add_of_lt'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_add_of_lt__04023416b8fe
