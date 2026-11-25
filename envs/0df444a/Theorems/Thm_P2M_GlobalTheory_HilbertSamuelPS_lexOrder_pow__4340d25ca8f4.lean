-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_pow__4340d25ca8f4
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_pow__4340d25ca8f4
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:47.415271+00:00
-- url     : https://prove2.me/theorems/4a06d7ae-f672-43ed-a800-377e3d7f0c06
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order pow  4340d25ca8f4: P2 M Global Theory Hilbert Samuel PS lex Order pow  4340d25ca8f4
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order pow  4340d25ca8f4 construction uses the P2 M Global Theory Hilbert Samuel PS lex Order pow  4340d25ca8f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L64-L69

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

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_pow__4340d25ca8f4 {g : MvPowerSeries (Fin D) ℂ} {e : Fin D →₀ ℕ}
    (he : lexOrder g = ((toLex e : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ)))) (k : ℕ) :
    lexOrder (g ^ k) = ((toLex (k • e) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_pow'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_pow__4340d25ca8f4
