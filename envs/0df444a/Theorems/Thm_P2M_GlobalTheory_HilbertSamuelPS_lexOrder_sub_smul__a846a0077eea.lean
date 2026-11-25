-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_sub_smul__a846a0077eea
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_sub_smul__a846a0077eea
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:52.411058+00:00
-- url     : https://prove2.me/theorems/67fc982c-5408-4c93-a0b2-fa17771113ee
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order sub smul  a846a0077eea: P2 M Global Theory Hilbert Samuel PS lex Order sub smul  a846a0077eea
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order sub smul  a846a0077eea construction uses the P2 M Global Theory Hilbert Samuel PS lex Order sub smul  a846a0077eea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L36-L48

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

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_sub_smul__a846a0077eea {g h : MvPowerSeries (Fin D) ℂ} (hg : g ≠ 0)
    (heq : lexOrder g = lexOrder h) : ∃ c : ℂ, lexOrder g < lexOrder (g - c • h) := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_sub_smul'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_sub_smul__a846a0077eea
