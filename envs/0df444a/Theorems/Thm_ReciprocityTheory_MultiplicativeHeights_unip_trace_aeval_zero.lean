-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_trace_aeval_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_trace_aeval_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:01.265173+00:00
-- url     : https://prove2.me/theorems/10116d7f-bf7e-5db6-befa-820a922f3145
-- title:
--   Multiplicative Heights: unip trace aeval zero
-- statement:
--   The Multiplicative Heights construction uses the unip trace aeval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentA.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentA.lean#L7-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial Matrix

theorem ReciprocityTheory.MultiplicativeHeights.unip_trace_aeval_zero {K : Type*} [Field K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval N P).trace = P.coeff 0 * r := by sorry
