-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_idem_eq_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_idem_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:12.889476+00:00
-- url     : https://prove2.me/theorems/7dc10470-6333-45b1-8845-4b715ad37125
-- title:
--   Multiplicative Heights: unip idem eq zero
-- statement:
--   The Multiplicative Heights construction uses the unip idem eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentA.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentA.lean#L16-L34

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

theorem ReciprocityTheory.MultiplicativeHeights.unip_idem_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (E : Matrix (Fin r) (Fin r) K)
    (hE : E * E = E) (ht : E.trace = 0) : E = 0 := by sorry
