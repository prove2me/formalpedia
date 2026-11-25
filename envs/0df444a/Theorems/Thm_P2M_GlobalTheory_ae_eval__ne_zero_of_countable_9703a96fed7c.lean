-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ae_eval__ne_zero_of_countable_9703a96fed7c
-- name    : P2M_GlobalTheory_ae_eval__ne_zero_of_countable_9703a96fed7c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:47.112662+00:00
-- url     : https://prove2.me/theorems/84874a09-2397-428a-80f9-cfe3d5edce62
-- title:
--   P2 M Global Theory ae eval  ne zero of countable 9703a96fed7c: P2 M Global Theory ae eval  ne zero of countable 9703a96fed7c
-- statement:
--   The P2 M Global Theory ae eval  ne zero of countable 9703a96fed7c construction uses the P2 M Global Theory ae eval  ne zero of countable 9703a96fed7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AeTranscendentalPointNonvanishing.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AeTranscendentalPointNonvanishing.lean#L8-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AeTranscendentalPointNonvanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem P2M_GlobalTheory_ae_eval__ne_zero_of_countable_9703a96fed7c (K : Type) [Field K] [Countable K] (σ : K →+* ℂ)
    (ι : Type) [Fintype ι] :
    ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by sorry

alias «GlobalTheory».«ae_eval₂_ne_zero_of_countable» := P2M_GlobalTheory_ae_eval__ne_zero_of_countable_9703a96fed7c
