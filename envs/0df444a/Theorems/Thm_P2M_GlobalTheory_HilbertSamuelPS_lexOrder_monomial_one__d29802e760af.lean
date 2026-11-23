-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HilbertSamuelPS_lexOrder_monomial_one__d29802e760af
-- name    : P2M_GlobalTheory_HilbertSamuelPS_lexOrder_monomial_one__d29802e760af
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:29.684232+00:00
-- url     : https://prove2.me/theorems/f3cad248-6cb2-48b4-b514-dbd1e7ea6e42
-- title:
--   P2 M Global Theory Hilbert Samuel PS lex Order monomial one  d29802e760af: P2 M Global Theory Hilbert Samuel PS lex Order monomial one  d29802e760af
-- statement:
--   The P2 M Global Theory Hilbert Samuel PS lex Order monomial one  d29802e760af construction uses the P2 M Global Theory Hilbert Samuel PS lex Order monomial one  d29802e760af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean#L50-L58

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

theorem P2M_GlobalTheory_HilbertSamuelPS_lexOrder_monomial_one__d29802e760af (a : Fin D →₀ ℕ) :
    lexOrder (monomial a (1 : ℂ)) = ((toLex a : Lex (Fin D →₀ ℕ)) : WithTop (Lex (Fin D →₀ ℕ))) := by sorry

alias «GlobalTheory».«HilbertSamuelPS».«lexOrder_monomial_one'» := P2M_GlobalTheory_HilbertSamuelPS_lexOrder_monomial_one__d29802e760af
