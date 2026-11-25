-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_coeff_top_le
-- name    : ReciprocityTheory.MultiplicativeHeights.log_norm_coeff_top_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:41.928804+00:00
-- url     : https://prove2.me/theorems/d33ff5b2-4f02-4058-9703-3a8acccb7a95
-- title:
--   Multiplicative Heights: log norm coeff top le
-- statement:
--   The Multiplicative Heights construction uses the log norm coeff top le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanA.lean#L45-L52

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

theorem ReciprocityTheory.MultiplicativeHeights.log_norm_coeff_top_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (htop : ∀ k', k < k' → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by sorry
