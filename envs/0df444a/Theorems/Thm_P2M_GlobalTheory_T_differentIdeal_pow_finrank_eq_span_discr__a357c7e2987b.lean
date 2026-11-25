-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_differentIdeal_pow_finrank_eq_span_discr__a357c7e2987b
-- name    : P2M_GlobalTheory_T_differentIdeal_pow_finrank_eq_span_discr__a357c7e2987b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:01.030058+00:00
-- url     : https://prove2.me/theorems/18fb550a-a061-45a4-b86e-52a14a1cced3
-- title:
--   P2 M Global Theory T different Ideal pow finrank eq span discr  a357c7e2987b: P2 M Global Theory T different Ideal pow finrank eq span discr  a357c7e2987b
-- statement:
--   The P2 M Global Theory T different Ideal pow finrank eq span discr  a357c7e2987b construction uses the P2 M Global Theory T different Ideal pow finrank eq span discr  a357c7e2987b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentIdealPowFinrankEqSpanDiscrStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentIdealPowFinrankEqSpanDiscrStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentIdealPowFinrankEqSpanDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentIdealPowFinrankEqSpanDiscrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_differentIdeal_pow_finrank_eq_span_discr__a357c7e2987b : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by sorry

alias «GlobalTheory».«T».«differentIdeal_pow_finrank_eq_span_discr'» := P2M_GlobalTheory_T_differentIdeal_pow_finrank_eq_span_discr__a357c7e2987b
