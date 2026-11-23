-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_one__aaa62325d311
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_one__aaa62325d311
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:02.136351+00:00
-- url     : https://prove2.me/theorems/ac11f8a7-23f0-4db1-be3d-452eb1a109bc
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order one  aaa62325d311: P2 M Global Theory Hilbert Samuel PS lex Order one  aaa62325d311
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order one  aaa62325d311 construction uses the P2 M Global Theory Hilbert Samuel PS lex Order one  aaa62325d311 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L60-L62

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

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_one__aaa62325d311 :
    lexOrder (1 : MvPowerSeries (Fin D) ℂ) = ((toLex (0 : Fin D →₀ ℕ) : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_one'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_one__aaa62325d311
