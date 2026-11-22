-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_eq_one_of_pow_eq_one
-- name    : ReciprocityTheory.Gal.eq_one_of_pow_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:52.249787+00:00
-- url     : https://prove2.me/theorems/d30d424d-4ac0-40f1-a7f5-5b88809ce2a9
-- title:
--   Gal: eq one of pow eq one
-- statement:
--   The Gal construction uses the eq one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L49-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L49-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {Ω : Type*} [Field Ω]

theorem ReciprocityTheory.Gal.eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {ξ : Ω} (hξ : ξ ^ N = 1) (h : A.valuation (ξ - 1) < 1) : ξ = 1 := by sorry
