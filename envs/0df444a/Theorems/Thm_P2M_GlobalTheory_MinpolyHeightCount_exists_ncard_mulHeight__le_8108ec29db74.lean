-- Prove2me | Theorems.Thm_P2M_GlobalTheory_MinpolyHeightCount_exists_ncard_mulHeight__le_8108ec29db74
-- name    : P2M_GlobalTheory_MinpolyHeightCount_exists_ncard_mulHeight__le_8108ec29db74
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:14.177793+00:00
-- url     : https://prove2.me/theorems/b93f4829-1578-42e4-a7d8-dafa3b7443b8
-- title:
--   P2 M Global Theory Minpoly Height Count exists ncard mul Height  le 8108ec29db74: P2 M Global Theory Minpoly Height Count exists ncard mul Height  le 8108ec29db74
-- statement:
--   The P2 M Global Theory Minpoly Height Count exists ncard mul Height  le 8108ec29db74 construction uses the P2 M Global Theory Minpoly Height Count exists ncard mul Height  le 8108ec29db74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L146-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L146-L190

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
variable (K)

theorem P2M_GlobalTheory_MinpolyHeightCount_exists_ncard_mulHeight__le_8108ec29db74 : ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
    {c : K | Height.mulHeight₁ c ≤ B}.Finite ∧
      (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by sorry

alias «GlobalTheory».«MinpolyHeightCount».«exists_ncard_mulHeight₁_le» := P2M_GlobalTheory_MinpolyHeightCount_exists_ncard_mulHeight__le_8108ec29db74
