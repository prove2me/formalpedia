-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_coeff_bot_le
-- name    : ReciprocityTheory.MultiplicativeHeights.log_norm_coeff_bot_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:41.118947+00:00
-- url     : https://prove2.me/theorems/f07bfebb-1e0c-478e-b39e-eb9fd85a44d6
-- title:
--   Multiplicative Heights: log norm coeff bot le
-- statement:
--   The Multiplicative Heights construction uses the log norm coeff bot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L54-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial Real

theorem ReciprocityTheory.MultiplicativeHeights.log_norm_coeff_bot_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (hbot : ∀ k', k' < k → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by sorry
