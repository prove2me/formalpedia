-- Prove2me | Theorems.Thm_P2M_GlobalTheory_MinpolyHeightCount_norm_embedding_le_mulHeight__593896cf91ef
-- name    : P2M_GlobalTheory_MinpolyHeightCount_norm_embedding_le_mulHeight__593896cf91ef
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:01.240725+00:00
-- url     : https://prove2.me/theorems/b559943a-2c82-4938-b70f-16e831dbd019
-- title:
--   P2 M Global Theory Minpoly Height Count norm embedding le mul Height  593896cf91ef: P2 M Global Theory Minpoly Height Count norm embedding le mul Height  593896cf91ef
-- statement:
--   The P2 M Global Theory Minpoly Height Count norm embedding le mul Height  593896cf91ef construction uses the P2 M Global Theory Minpoly Height Count norm embedding le mul Height  593896cf91ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L129-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L129-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GlobalTheory_MinpolyHeightCount_norm_embedding_le_mulHeight__593896cf91ef (φ : K →+* ℂ) (c : K) : ‖φ c‖ ≤ Height.mulHeight₁ c := by sorry

alias «GlobalTheory».«MinpolyHeightCount».«norm_embedding_le_mulHeight₁» := P2M_GlobalTheory_MinpolyHeightCount_norm_embedding_le_mulHeight__593896cf91ef
