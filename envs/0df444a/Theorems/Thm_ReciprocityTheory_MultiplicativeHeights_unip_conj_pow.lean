-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_conj_pow
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_conj_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:06.442045+00:00
-- url     : https://prove2.me/theorems/5778834c-f320-48c6-a578-687516fb2f42
-- title:
--   Multiplicative Heights: unip conj pow
-- statement:
--   The Multiplicative Heights construction uses the unip conj pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/Unipotent.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/Unipotent.lean#L8-L18

import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.unip_conj_pow {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) (n : ℕ) :
    (Q * M * Q⁻¹) ^ n = Q * M ^ n * Q⁻¹ := by sorry
