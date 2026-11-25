-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_unitary_mul_upper
-- name    : ReciprocityTheory.MultiplicativeHeights.exists_unitary_mul_upper
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:10.334033+00:00
-- url     : https://prove2.me/theorems/44e73d12-fed5-53f4-a430-eec1bfd6b9de
-- title:
--   Multiplicative Heights: exists unitary mul upper
-- statement:
--   The Multiplicative Heights construction uses the exists unitary mul upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LemmaH.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LemmaH.lean#L7-L33

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_LemmaH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix InnerProductSpace

theorem ReciprocityTheory.MultiplicativeHeights.exists_unitary_mul_upper {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∃ k b : Matrix (Fin n) (Fin n) ℂ, k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ b.BlockTriangular id ∧
      x = k * b ∧ ∀ j, ‖b j j‖ ^ 2 ≤ colNormSq x j := by sorry
