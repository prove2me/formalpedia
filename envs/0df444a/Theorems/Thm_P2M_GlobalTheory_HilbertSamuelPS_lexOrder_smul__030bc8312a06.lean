-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_smul__030bc8312a06
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_smul__030bc8312a06
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:53.341853+00:00
-- url     : https://prove2.me/theorems/b099d43f-cab2-4030-bbff-4f5c46c58430
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order smul  030bc8312a06: P2 M Global Theory Hilbert Samuel PS lex Order smul  030bc8312a06
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order smul  030bc8312a06 construction uses the P2 M Global Theory Hilbert Samuel PS lex Order smul  030bc8312a06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L20-L22

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

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_smul__030bc8312a06 {c : ℂ} (hc : c ≠ 0) (g : MvPowerSeries (Fin D) ℂ) :
    lexOrder (c • g) = lexOrder g := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_smul'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_smul__030bc8312a06
