-- Prove2me | Theorems.Thm_UpperTheory_Ram_cond_le_four_n_sq
-- name    : UpperTheory.Ram.cond_le_four_n_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:59.120847+00:00
-- url     : https://prove2.me/theorems/d13112d0-95ea-4cf9-837d-69382450c4b1
-- title:
--   Ram: cond le four n sq
-- statement:
--   The Ram construction uses the cond le four n sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondLam.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/CondLam.lean#L7-L39

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeTotientQS
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions

theorem UpperTheory.Ram.cond_le_four_n_sq :
    ∀ (R : Ranks) (H : Host R), (H.QS : ℝ) * H.q * H.d ≤ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ∧ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ≤ ((H.QS : ℝ) * H.q * H.d) ^ 2 ∧ (R.f : ℝ) ≤ H.QS := by sorry
