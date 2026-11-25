-- Prove2me | Theorems.Thm_UpperTheory_WildA_logSum
-- name    : UpperTheory.WildA.logSum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:10.790516+00:00
-- url     : https://prove2.me/theorems/16dc8344-bccc-4f96-9b8d-7297aaf01f70
-- title:
--   Wild A: log Sum
-- statement:
--   The Wild A construction uses the log Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/WildJets/LogSum.lean#L3-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/WildJets/LogSum.lean#L3-L24

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_WildJets_LogSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.WildA.logSum :
    ∀ y : ℝ, 1 ≤ y → ∑ l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.logb l y * Real.log l ≤ y * Real.log y := by sorry
