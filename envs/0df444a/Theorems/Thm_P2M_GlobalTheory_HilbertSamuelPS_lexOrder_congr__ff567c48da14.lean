-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_congr__ff567c48da14
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_congr__ff567c48da14
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:03.93252+00:00
-- url     : https://prove2.me/theorems/e4280790-0961-4e69-8e29-84b376846f74
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order congr  ff567c48da14: P2 M Global Theory Hilbert Samuel PS lex Order congr  ff567c48da14
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order congr  ff567c48da14 construction uses the P2 M Global Theory Hilbert Samuel PS lex Order congr  ff567c48da14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L15-L18

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

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_congr__ff567c48da14 {g h : MvPowerSeries (Fin D) ℂ}
    (H : ∀ d, coeff d g = 0 ↔ coeff d h = 0) : lexOrder g = lexOrder h := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_congr'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_congr__ff567c48da14
