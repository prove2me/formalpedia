-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_prod_X_pow__790a47b3fadf
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_prod_X_pow__790a47b3fadf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:21.217695+00:00
-- url     : https://prove2.me/theorems/feba1a4c-3723-4f62-817b-befc0c8dbe10
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order prod X pow  790a47b3fadf: P2 M Global Theory Hilbert Samuel PS lex Order prod X pow  790a47b3fadf
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order prod X pow  790a47b3fadf construction uses the P2 M Global Theory Hilbert Samuel PS lex Order prod X pow  790a47b3fadf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L71-L82

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

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_prod_X_pow__790a47b3fadf (a : Fin D → ℕ) :
    lexOrder (∏ i, (X i : MvPowerSeries (Fin D) ℂ) ^ a i) =
      ((toLex (∑ i, Finsupp.single i (a i)) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_prod_X_pow'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_prod_X_pow__790a47b3fadf
