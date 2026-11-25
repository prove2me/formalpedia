-- Prove2me | Theorems.Thm_UpperTheory_torsionOrder_le_two_mul_finrank_sq
-- name    : UpperTheory.torsionOrder_le_two_mul_finrank_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:19.809907+00:00
-- url     : https://prove2.me/theorems/fa8248bb-b74d-4f50-9505-39ff31373e41
-- title:
--   Upper Theory: torsion Order le two mul finrank sq
-- statement:
--   The Upper Theory construction uses the torsion Order le two mul finrank sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/TorsionOrderLeTwoMulFinrankSq.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/TorsionOrderLeTwoMulFinrankSq.lean#L85-L88

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_TorsionOrderLeTwoMulFinrankSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField

theorem UpperTheory.torsionOrder_le_two_mul_finrank_sq :
    ∀ (E : Type) [Field E] [NumberField E], NumberField.Units.torsionOrder E ≤ 2 * Module.finrank ℚ E ^ 2 := by sorry
